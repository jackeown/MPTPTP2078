%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  219 (8647 expanded)
%              Number of leaves         :   18 (1745 expanded)
%              Depth                    :   30
%              Number of atoms          : 1053 (74296 expanded)
%              Number of equality atoms :   80 (7828 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3102,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3101,f2862])).

fof(f2862,plain,(
    r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),sK5) ),
    inference(backward_demodulation,[],[f94,f2861])).

fof(f2861,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_tmap_1(sK2,sK1,sK4,sK2) ),
    inference(forward_demodulation,[],[f2860,f2657])).

fof(f2657,plain,(
    k2_tmap_1(sK2,sK1,sK4,sK2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f2655,f115])).

fof(f115,plain,(
    u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(resolution,[],[f100,f105])).

fof(f105,plain,(
    l1_pre_topc(sK2) ),
    inference(resolution,[],[f102,f58])).

fof(f58,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
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
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
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
                       => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                      & X5 = X6 )
                                   => r1_tmap_1(X3,X1,X4,X5) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
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
                     => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                    & X5 = X6 )
                                 => r1_tmap_1(X3,X1,X4,X5) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tmap_1)).

fof(f102,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK0)
      | l1_pre_topc(X1) ) ),
    inference(resolution,[],[f70,f64])).

fof(f64,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f100,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(resolution,[],[f65,f66])).

fof(f66,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f65,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f2655,plain,(
    k2_tmap_1(sK2,sK1,sK4,sK2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    inference(resolution,[],[f2649,f110])).

fof(f110,plain,(
    m1_pre_topc(sK2,sK2) ),
    inference(resolution,[],[f105,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f2649,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK2)
      | k2_tmap_1(sK2,sK1,sK4,X2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f2648,f137])).

fof(f137,plain,(
    v2_pre_topc(sK2) ),
    inference(resolution,[],[f134,f58])).

% (22503)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
fof(f134,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f130,f63])).

fof(f63,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f130,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_pre_topc(X0) ) ),
    inference(resolution,[],[f81,f64])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f2648,plain,(
    ! [X2] :
      ( ~ v2_pre_topc(sK2)
      | ~ m1_pre_topc(X2,sK2)
      | k2_tmap_1(sK2,sK1,sK4,X2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f2647,f403])).

fof(f403,plain,(
    v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f122,f400])).

fof(f400,plain,(
    k2_struct_0(sK2) = k2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f394,f110])).

fof(f394,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | k2_struct_0(sK2) = k2_struct_0(sK3) ),
    inference(resolution,[],[f383,f253])).

fof(f253,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | k2_struct_0(sK2) = k2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f195,f252])).

fof(f252,plain,(
    r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f178,f249])).

fof(f249,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(resolution,[],[f247,f108])).

fof(f108,plain,(
    m1_pre_topc(sK3,sK3) ),
    inference(resolution,[],[f104,f67])).

fof(f104,plain,(
    l1_pre_topc(sK3) ),
    inference(resolution,[],[f102,f56])).

fof(f56,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f247,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK3)
      | m1_pre_topc(X2,sK2) ) ),
    inference(forward_demodulation,[],[f246,f120])).

fof(f120,plain,(
    sK3 = g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(backward_demodulation,[],[f54,f115])).

fof(f54,plain,(
    sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f246,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)))
      | m1_pre_topc(X2,sK2) ) ),
    inference(forward_demodulation,[],[f242,f115])).

fof(f242,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | m1_pre_topc(X2,sK2) ) ),
    inference(resolution,[],[f73,f105])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

fof(f178,plain,
    ( r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2))
    | ~ m1_pre_topc(sK3,sK2) ),
    inference(superposition,[],[f158,f116])).

fof(f116,plain,(
    u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(resolution,[],[f100,f104])).

fof(f158,plain,(
    ! [X2] :
      ( r1_tarski(u1_struct_0(X2),k2_struct_0(sK2))
      | ~ m1_pre_topc(X2,sK2) ) ),
    inference(subsumption_resolution,[],[f154,f105])).

fof(f154,plain,(
    ! [X2] :
      ( r1_tarski(u1_struct_0(X2),k2_struct_0(sK2))
      | ~ m1_pre_topc(X2,sK2)
      | ~ l1_pre_topc(sK2) ) ),
    inference(superposition,[],[f71,f115])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(f195,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2))
    | k2_struct_0(sK2) = k2_struct_0(sK3) ),
    inference(resolution,[],[f182,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f182,plain,
    ( r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK3) ),
    inference(superposition,[],[f159,f115])).

fof(f159,plain,(
    ! [X3] :
      ( r1_tarski(u1_struct_0(X3),k2_struct_0(sK3))
      | ~ m1_pre_topc(X3,sK3) ) ),
    inference(subsumption_resolution,[],[f155,f104])).

fof(f155,plain,(
    ! [X3] :
      ( r1_tarski(u1_struct_0(X3),k2_struct_0(sK3))
      | ~ m1_pre_topc(X3,sK3)
      | ~ l1_pre_topc(sK3) ) ),
    inference(superposition,[],[f71,f116])).

fof(f383,plain,(
    ! [X2] :
      ( m1_pre_topc(X2,sK3)
      | ~ m1_pre_topc(X2,sK2) ) ),
    inference(forward_demodulation,[],[f382,f120])).

fof(f382,plain,(
    ! [X2] :
      ( m1_pre_topc(X2,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)))
      | ~ m1_pre_topc(X2,sK2) ) ),
    inference(forward_demodulation,[],[f381,f115])).

fof(f381,plain,(
    ! [X2] :
      ( m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | ~ m1_pre_topc(X2,sK2) ) ),
    inference(subsumption_resolution,[],[f375,f109])).

fof(f109,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f105,f70])).

fof(f375,plain,(
    ! [X2] :
      ( ~ l1_pre_topc(X2)
      | m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | ~ m1_pre_topc(X2,sK2) ) ),
    inference(resolution,[],[f69,f105])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f122,plain,(
    v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f117,f116])).

fof(f117,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f52,f114])).

fof(f114,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f100,f61])).

fof(f61,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f52,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f2647,plain,(
    ! [X2] :
      ( ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
      | ~ v2_pre_topc(sK2)
      | ~ m1_pre_topc(X2,sK2)
      | k2_tmap_1(sK2,sK1,sK4,X2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f2646,f57])).

fof(f57,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f2646,plain,(
    ! [X2] :
      ( v2_struct_0(sK2)
      | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
      | ~ v2_pre_topc(sK2)
      | ~ m1_pre_topc(X2,sK2)
      | k2_tmap_1(sK2,sK1,sK4,X2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f2645,f105])).

fof(f2645,plain,(
    ! [X2] :
      ( ~ l1_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
      | ~ v2_pre_topc(sK2)
      | ~ m1_pre_topc(X2,sK2)
      | k2_tmap_1(sK2,sK1,sK4,X2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f2643,f402])).

fof(f402,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f121,f400])).

fof(f121,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f118,f116])).

fof(f118,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f53,f114])).

fof(f53,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f21])).

fof(f2643,plain,(
    ! [X2] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))))
      | ~ l1_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
      | ~ v2_pre_topc(sK2)
      | ~ m1_pre_topc(X2,sK2)
      | k2_tmap_1(sK2,sK1,sK4,X2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X2)) ) ),
    inference(superposition,[],[f1668,f115])).

fof(f1668,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),k2_struct_0(sK1))))
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ v1_funct_2(sK4,u1_struct_0(X2),k2_struct_0(sK1))
      | ~ v2_pre_topc(X2)
      | ~ m1_pre_topc(X3,X2)
      | k2_tmap_1(X2,sK1,sK4,X3) = k2_partfun1(u1_struct_0(X2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f1667,f61])).

fof(f1667,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),k2_struct_0(sK1))))
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(X2)
      | ~ v1_funct_2(sK4,u1_struct_0(X2),k2_struct_0(sK1))
      | ~ v2_pre_topc(X2)
      | ~ m1_pre_topc(X3,X2)
      | k2_tmap_1(X2,sK1,sK4,X3) = k2_partfun1(u1_struct_0(X2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f1666,f60])).

fof(f60,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f1666,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),k2_struct_0(sK1))))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(X2)
      | ~ v1_funct_2(sK4,u1_struct_0(X2),k2_struct_0(sK1))
      | ~ v2_pre_topc(X2)
      | ~ m1_pre_topc(X3,X2)
      | k2_tmap_1(X2,sK1,sK4,X3) = k2_partfun1(u1_struct_0(X2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f1648,f59])).

fof(f59,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f1648,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),k2_struct_0(sK1))))
      | ~ l1_pre_topc(X2)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(X2)
      | ~ v1_funct_2(sK4,u1_struct_0(X2),k2_struct_0(sK1))
      | ~ v2_pre_topc(X2)
      | ~ m1_pre_topc(X3,X2)
      | k2_tmap_1(X2,sK1,sK4,X3) = k2_partfun1(u1_struct_0(X2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) ) ),
    inference(superposition,[],[f876,f114])).

fof(f876,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X0)
      | ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X2,X0)
      | k2_tmap_1(X0,X1,sK4,X2) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) ) ),
    inference(resolution,[],[f75,f51])).

fof(f51,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f21])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X0)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X0)
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

% (22506)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f2860,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f2857,f115])).

fof(f2857,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    inference(resolution,[],[f2848,f2125])).

fof(f2125,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f2124,f55])).

fof(f55,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f2124,plain,
    ( m1_pre_topc(sK2,sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f2119,f249])).

fof(f2119,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | m1_pre_topc(sK2,sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f2105,f108])).

fof(f2105,plain,(
    ! [X12] :
      ( ~ m1_pre_topc(sK3,X12)
      | ~ m1_pre_topc(X12,sK2)
      | m1_pre_topc(sK2,X12)
      | v2_struct_0(X12) ) ),
    inference(subsumption_resolution,[],[f2104,f57])).

fof(f2104,plain,(
    ! [X12] :
      ( v2_struct_0(X12)
      | ~ m1_pre_topc(X12,sK2)
      | v2_struct_0(sK2)
      | m1_pre_topc(sK2,X12)
      | ~ m1_pre_topc(sK3,X12) ) ),
    inference(subsumption_resolution,[],[f2103,f110])).

fof(f2103,plain,(
    ! [X12] :
      ( ~ m1_pre_topc(sK2,sK2)
      | v2_struct_0(X12)
      | ~ m1_pre_topc(X12,sK2)
      | v2_struct_0(sK2)
      | m1_pre_topc(sK2,X12)
      | ~ m1_pre_topc(sK3,X12) ) ),
    inference(subsumption_resolution,[],[f2102,f137])).

fof(f2102,plain,(
    ! [X12] :
      ( ~ v2_pre_topc(sK2)
      | ~ m1_pre_topc(sK2,sK2)
      | v2_struct_0(X12)
      | ~ m1_pre_topc(X12,sK2)
      | v2_struct_0(sK2)
      | m1_pre_topc(sK2,X12)
      | ~ m1_pre_topc(sK3,X12) ) ),
    inference(subsumption_resolution,[],[f2071,f105])).

fof(f2071,plain,(
    ! [X12] :
      ( ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | ~ m1_pre_topc(sK2,sK2)
      | v2_struct_0(X12)
      | ~ m1_pre_topc(X12,sK2)
      | v2_struct_0(sK2)
      | m1_pre_topc(sK2,X12)
      | ~ m1_pre_topc(sK3,X12) ) ),
    inference(resolution,[],[f2062,f556])).

fof(f556,plain,(
    v1_tsep_1(sK2,sK2) ),
    inference(subsumption_resolution,[],[f555,f110])).

fof(f555,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | v1_tsep_1(sK2,sK2) ),
    inference(subsumption_resolution,[],[f553,f142])).

fof(f142,plain,(
    v3_pre_topc(k2_struct_0(sK2),sK2) ),
    inference(subsumption_resolution,[],[f126,f137])).

fof(f126,plain,
    ( v3_pre_topc(k2_struct_0(sK2),sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(resolution,[],[f80,f105])).

fof(f80,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(k2_struct_0(X0),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f553,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK2),sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | v1_tsep_1(sK2,sK2) ),
    inference(superposition,[],[f535,f115])).

fof(f535,plain,(
    ! [X2] :
      ( ~ v3_pre_topc(u1_struct_0(X2),sK2)
      | ~ m1_pre_topc(X2,sK2)
      | v1_tsep_1(X2,sK2) ) ),
    inference(subsumption_resolution,[],[f531,f137])).

fof(f531,plain,(
    ! [X2] :
      ( ~ v2_pre_topc(sK2)
      | ~ m1_pre_topc(X2,sK2)
      | ~ v3_pre_topc(u1_struct_0(X2),sK2)
      | v1_tsep_1(X2,sK2) ) ),
    inference(resolution,[],[f96,f105])).

% (22491)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
fof(f96,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f90,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | ~ v3_pre_topc(X2,X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).

fof(f2062,plain,(
    ! [X0,X1] :
      ( ~ v1_tsep_1(sK2,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(sK2,X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | m1_pre_topc(sK2,X1)
      | ~ m1_pre_topc(sK3,X1) ) ),
    inference(subsumption_resolution,[],[f2055,f70])).

fof(f2055,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_tsep_1(sK2,X0)
      | ~ m1_pre_topc(sK2,X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | m1_pre_topc(sK2,X1)
      | ~ m1_pre_topc(sK3,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f781,f406])).

fof(f406,plain,(
    ! [X3] :
      ( r1_tarski(k2_struct_0(sK2),u1_struct_0(X3))
      | ~ m1_pre_topc(sK3,X3)
      | ~ l1_pre_topc(X3) ) ),
    inference(backward_demodulation,[],[f151,f400])).

fof(f151,plain,(
    ! [X3] :
      ( r1_tarski(k2_struct_0(sK3),u1_struct_0(X3))
      | ~ m1_pre_topc(sK3,X3)
      | ~ l1_pre_topc(X3) ) ),
    inference(superposition,[],[f71,f116])).

fof(f781,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(k2_struct_0(sK2),u1_struct_0(X4))
      | ~ v2_pre_topc(X5)
      | ~ l1_pre_topc(X5)
      | ~ v1_tsep_1(sK2,X5)
      | ~ m1_pre_topc(sK2,X5)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,X5)
      | v2_struct_0(X5)
      | m1_pre_topc(sK2,X4) ) ),
    inference(superposition,[],[f79,f115])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0)
      | m1_pre_topc(X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
                & v1_tsep_1(X1,X2) )
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
                & v1_tsep_1(X1,X2) )
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v1_tsep_1(X1,X0) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
               => ( m1_pre_topc(X1,X2)
                  & v1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tsep_1)).

fof(f2848,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(X3,sK3)
      | k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) = k3_tmap_1(sK0,sK1,sK3,X3,sK4) ) ),
    inference(subsumption_resolution,[],[f2847,f63])).

fof(f2847,plain,(
    ! [X3] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X3,sK3)
      | k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) = k3_tmap_1(sK0,sK1,sK3,X3,sK4) ) ),
    inference(subsumption_resolution,[],[f2846,f62])).

fof(f62,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f2846,plain,(
    ! [X3] :
      ( v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X3,sK3)
      | k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) = k3_tmap_1(sK0,sK1,sK3,X3,sK4) ) ),
    inference(subsumption_resolution,[],[f2840,f64])).

fof(f2840,plain,(
    ! [X3] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X3,sK3)
      | k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) = k3_tmap_1(sK0,sK1,sK3,X3,sK4) ) ),
    inference(resolution,[],[f2800,f56])).

fof(f2800,plain,(
    ! [X6,X7] :
      ( ~ m1_pre_topc(sK3,X6)
      | ~ l1_pre_topc(X6)
      | v2_struct_0(X6)
      | ~ v2_pre_topc(X6)
      | ~ m1_pre_topc(X7,sK3)
      | k3_tmap_1(X6,sK1,sK3,X7,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X7)) ) ),
    inference(subsumption_resolution,[],[f2799,f403])).

fof(f2799,plain,(
    ! [X6,X7] :
      ( ~ l1_pre_topc(X6)
      | ~ m1_pre_topc(sK3,X6)
      | v2_struct_0(X6)
      | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
      | ~ v2_pre_topc(X6)
      | ~ m1_pre_topc(X7,sK3)
      | k3_tmap_1(X6,sK1,sK3,X7,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X7)) ) ),
    inference(subsumption_resolution,[],[f2796,f402])).

fof(f2796,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))))
      | ~ l1_pre_topc(X6)
      | ~ m1_pre_topc(sK3,X6)
      | v2_struct_0(X6)
      | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
      | ~ v2_pre_topc(X6)
      | ~ m1_pre_topc(X7,sK3)
      | k3_tmap_1(X6,sK1,sK3,X7,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X7)) ) ),
    inference(superposition,[],[f2008,f401])).

fof(f401,plain,(
    u1_struct_0(sK3) = k2_struct_0(sK2) ),
    inference(backward_demodulation,[],[f116,f400])).

fof(f2008,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1))))
      | ~ l1_pre_topc(X4)
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X4)
      | ~ v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1))
      | ~ v2_pre_topc(X4)
      | ~ m1_pre_topc(X5,X3)
      | k3_tmap_1(X4,sK1,X3,X5,sK4) = k2_partfun1(u1_struct_0(X3),k2_struct_0(sK1),sK4,u1_struct_0(X5)) ) ),
    inference(subsumption_resolution,[],[f2007,f61])).

fof(f2007,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1))))
      | ~ l1_pre_topc(X4)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X4)
      | ~ v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1))
      | ~ v2_pre_topc(X4)
      | ~ m1_pre_topc(X5,X3)
      | k3_tmap_1(X4,sK1,X3,X5,sK4) = k2_partfun1(u1_struct_0(X3),k2_struct_0(sK1),sK4,u1_struct_0(X5)) ) ),
    inference(subsumption_resolution,[],[f2006,f60])).

fof(f2006,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1))))
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X4)
      | ~ v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1))
      | ~ v2_pre_topc(X4)
      | ~ m1_pre_topc(X5,X3)
      | k3_tmap_1(X4,sK1,X3,X5,sK4) = k2_partfun1(u1_struct_0(X3),k2_struct_0(sK1),sK4,u1_struct_0(X5)) ) ),
    inference(subsumption_resolution,[],[f2000,f59])).

fof(f2000,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1))))
      | ~ l1_pre_topc(X4)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X4)
      | ~ v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1))
      | ~ v2_pre_topc(X4)
      | ~ m1_pre_topc(X5,X3)
      | k3_tmap_1(X4,sK1,X3,X5,sK4) = k2_partfun1(u1_struct_0(X3),k2_struct_0(sK1),sK4,u1_struct_0(X5)) ) ),
    inference(superposition,[],[f1090,f114])).

fof(f1090,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0)
      | ~ v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X3,X2)
      | k3_tmap_1(X0,X1,X2,X3,sK4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),sK4,u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f1089,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f1089,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X0)
      | ~ v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X2)
      | k3_tmap_1(X0,X1,X2,X3,sK4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),sK4,u1_struct_0(X3)) ) ),
    inference(resolution,[],[f74,f51])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X0)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X2)
      | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f94,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(backward_demodulation,[],[f48,f47])).

fof(f47,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f21])).

fof(f48,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f21])).

fof(f3101,plain,(
    ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),sK5) ),
    inference(forward_demodulation,[],[f3100,f2666])).

fof(f2666,plain,(
    k2_tmap_1(sK2,sK1,sK4,sK2) = k2_tmap_1(sK3,sK1,sK4,sK2) ),
    inference(forward_demodulation,[],[f2665,f2657])).

fof(f2665,plain,(
    k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,k2_struct_0(sK2)) = k2_tmap_1(sK3,sK1,sK4,sK2) ),
    inference(forward_demodulation,[],[f2662,f115])).

fof(f2662,plain,(
    k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,sK4,sK2) ),
    inference(resolution,[],[f2654,f2125])).

fof(f2654,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(X3,sK3)
      | k2_tmap_1(sK3,sK1,sK4,X3) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f2653,f136])).

fof(f136,plain,(
    v2_pre_topc(sK3) ),
    inference(resolution,[],[f134,f56])).

fof(f2653,plain,(
    ! [X3] :
      ( ~ v2_pre_topc(sK3)
      | ~ m1_pre_topc(X3,sK3)
      | k2_tmap_1(sK3,sK1,sK4,X3) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f2652,f403])).

fof(f2652,plain,(
    ! [X3] :
      ( ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
      | ~ v2_pre_topc(sK3)
      | ~ m1_pre_topc(X3,sK3)
      | k2_tmap_1(sK3,sK1,sK4,X3) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f2651,f55])).

fof(f2651,plain,(
    ! [X3] :
      ( v2_struct_0(sK3)
      | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
      | ~ v2_pre_topc(sK3)
      | ~ m1_pre_topc(X3,sK3)
      | k2_tmap_1(sK3,sK1,sK4,X3) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f2650,f104])).

fof(f2650,plain,(
    ! [X3] :
      ( ~ l1_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
      | ~ v2_pre_topc(sK3)
      | ~ m1_pre_topc(X3,sK3)
      | k2_tmap_1(sK3,sK1,sK4,X3) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f2644,f402])).

fof(f2644,plain,(
    ! [X3] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))))
      | ~ l1_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
      | ~ v2_pre_topc(sK3)
      | ~ m1_pre_topc(X3,sK3)
      | k2_tmap_1(sK3,sK1,sK4,X3) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) ) ),
    inference(superposition,[],[f1668,f401])).

fof(f3100,plain,(
    ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK5) ),
    inference(subsumption_resolution,[],[f3099,f1495])).

fof(f1495,plain,(
    v1_tsep_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f1494,f57])).

fof(f1494,plain,
    ( v2_struct_0(sK2)
    | v1_tsep_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f1493,f249])).

fof(f1493,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK2)
    | v1_tsep_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f1492,f110])).

fof(f1492,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK2)
    | v1_tsep_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f1491,f137])).

fof(f1491,plain,
    ( ~ v2_pre_topc(sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK2)
    | v1_tsep_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f1469,f105])).

fof(f1469,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK2)
    | v1_tsep_1(sK2,sK3) ),
    inference(resolution,[],[f1279,f556])).

fof(f1279,plain,(
    ! [X2] :
      ( ~ v1_tsep_1(sK2,X2)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ m1_pre_topc(sK2,X2)
      | ~ m1_pre_topc(sK3,X2)
      | v2_struct_0(X2)
      | v1_tsep_1(sK2,sK3) ) ),
    inference(subsumption_resolution,[],[f1275,f92])).

fof(f92,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1275,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_struct_0(sK2),k2_struct_0(sK2))
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | ~ v1_tsep_1(sK2,X2)
      | ~ m1_pre_topc(sK2,X2)
      | ~ m1_pre_topc(sK3,X2)
      | v2_struct_0(X2)
      | v1_tsep_1(sK2,sK3) ) ),
    inference(superposition,[],[f669,f115])).

fof(f669,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(u1_struct_0(X6),k2_struct_0(sK2))
      | ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | ~ v1_tsep_1(X6,X7)
      | ~ m1_pre_topc(X6,X7)
      | ~ m1_pre_topc(sK3,X7)
      | v2_struct_0(X7)
      | v1_tsep_1(X6,sK3) ) ),
    inference(subsumption_resolution,[],[f662,f55])).

fof(f662,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(u1_struct_0(X6),k2_struct_0(sK2))
      | ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | ~ v1_tsep_1(X6,X7)
      | ~ m1_pre_topc(X6,X7)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,X7)
      | v2_struct_0(X7)
      | v1_tsep_1(X6,sK3) ) ),
    inference(superposition,[],[f78,f401])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0)
      | v1_tsep_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f3099,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK5) ),
    inference(subsumption_resolution,[],[f3098,f57])).

fof(f3098,plain,
    ( v2_struct_0(sK2)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK5) ),
    inference(subsumption_resolution,[],[f3097,f2125])).

fof(f3097,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(sK2)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK5) ),
    inference(subsumption_resolution,[],[f3093,f119])).

fof(f119,plain,(
    m1_subset_1(sK5,k2_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f95,f115])).

fof(f95,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f46,f47])).

fof(f46,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f3093,plain,
    ( ~ m1_subset_1(sK5,k2_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(sK2)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK5) ),
    inference(superposition,[],[f3090,f115])).

fof(f3090,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK5,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,sK3)
      | v2_struct_0(X0)
      | ~ v1_tsep_1(X0,sK3)
      | ~ r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),sK5) ) ),
    inference(subsumption_resolution,[],[f3089,f49])).

fof(f49,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f21])).

fof(f3089,plain,(
    ! [X0] :
      ( ~ v1_tsep_1(X0,sK3)
      | ~ m1_pre_topc(X0,sK3)
      | v2_struct_0(X0)
      | ~ m1_subset_1(sK5,u1_struct_0(X0))
      | ~ r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),sK5)
      | r1_tmap_1(sK3,sK1,sK4,sK5) ) ),
    inference(resolution,[],[f3060,f119])).

fof(f3060,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X7,k2_struct_0(sK2))
      | ~ v1_tsep_1(X6,sK3)
      | ~ m1_pre_topc(X6,sK3)
      | v2_struct_0(X6)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ r1_tmap_1(X6,sK1,k2_tmap_1(sK3,sK1,sK4,X6),X7)
      | r1_tmap_1(sK3,sK1,sK4,X7) ) ),
    inference(subsumption_resolution,[],[f3059,f403])).

fof(f3059,plain,(
    ! [X6,X7] :
      ( ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
      | v2_struct_0(X6)
      | ~ v1_tsep_1(X6,sK3)
      | ~ m1_pre_topc(X6,sK3)
      | ~ m1_subset_1(X7,k2_struct_0(sK2))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ r1_tmap_1(X6,sK1,k2_tmap_1(sK3,sK1,sK4,X6),X7)
      | r1_tmap_1(sK3,sK1,sK4,X7) ) ),
    inference(subsumption_resolution,[],[f3058,f104])).

fof(f3058,plain,(
    ! [X6,X7] :
      ( ~ l1_pre_topc(sK3)
      | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
      | v2_struct_0(X6)
      | ~ v1_tsep_1(X6,sK3)
      | ~ m1_pre_topc(X6,sK3)
      | ~ m1_subset_1(X7,k2_struct_0(sK2))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ r1_tmap_1(X6,sK1,k2_tmap_1(sK3,sK1,sK4,X6),X7)
      | r1_tmap_1(sK3,sK1,sK4,X7) ) ),
    inference(subsumption_resolution,[],[f3057,f136])).

fof(f3057,plain,(
    ! [X6,X7] :
      ( ~ v2_pre_topc(sK3)
      | ~ l1_pre_topc(sK3)
      | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
      | v2_struct_0(X6)
      | ~ v1_tsep_1(X6,sK3)
      | ~ m1_pre_topc(X6,sK3)
      | ~ m1_subset_1(X7,k2_struct_0(sK2))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ r1_tmap_1(X6,sK1,k2_tmap_1(sK3,sK1,sK4,X6),X7)
      | r1_tmap_1(sK3,sK1,sK4,X7) ) ),
    inference(subsumption_resolution,[],[f3056,f55])).

fof(f3056,plain,(
    ! [X6,X7] :
      ( v2_struct_0(sK3)
      | ~ v2_pre_topc(sK3)
      | ~ l1_pre_topc(sK3)
      | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
      | v2_struct_0(X6)
      | ~ v1_tsep_1(X6,sK3)
      | ~ m1_pre_topc(X6,sK3)
      | ~ m1_subset_1(X7,k2_struct_0(sK2))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ r1_tmap_1(X6,sK1,k2_tmap_1(sK3,sK1,sK4,X6),X7)
      | r1_tmap_1(sK3,sK1,sK4,X7) ) ),
    inference(subsumption_resolution,[],[f3050,f402])).

fof(f3050,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))))
      | v2_struct_0(sK3)
      | ~ v2_pre_topc(sK3)
      | ~ l1_pre_topc(sK3)
      | ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
      | v2_struct_0(X6)
      | ~ v1_tsep_1(X6,sK3)
      | ~ m1_pre_topc(X6,sK3)
      | ~ m1_subset_1(X7,k2_struct_0(sK2))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ r1_tmap_1(X6,sK1,k2_tmap_1(sK3,sK1,sK4,X6),X7)
      | r1_tmap_1(sK3,sK1,sK4,X7) ) ),
    inference(superposition,[],[f2412,f401])).

fof(f2412,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1))))
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | ~ v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1))
      | v2_struct_0(X4)
      | ~ v1_tsep_1(X4,X3)
      | ~ m1_pre_topc(X4,X3)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ r1_tmap_1(X4,sK1,k2_tmap_1(X3,sK1,sK4,X4),X5)
      | r1_tmap_1(X3,sK1,sK4,X5) ) ),
    inference(subsumption_resolution,[],[f2411,f60])).

fof(f2411,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1))))
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | ~ v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1))
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(X4)
      | ~ v1_tsep_1(X4,X3)
      | ~ m1_pre_topc(X4,X3)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ r1_tmap_1(X4,sK1,k2_tmap_1(X3,sK1,sK4,X4),X5)
      | r1_tmap_1(X3,sK1,sK4,X5) ) ),
    inference(subsumption_resolution,[],[f2410,f59])).

fof(f2410,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1))))
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | v2_struct_0(sK1)
      | ~ v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1))
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(X4)
      | ~ v1_tsep_1(X4,X3)
      | ~ m1_pre_topc(X4,X3)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ r1_tmap_1(X4,sK1,k2_tmap_1(X3,sK1,sK4,X4),X5)
      | r1_tmap_1(X3,sK1,sK4,X5) ) ),
    inference(subsumption_resolution,[],[f2392,f61])).

fof(f2392,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1))))
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | v2_struct_0(sK1)
      | ~ v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1))
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(X4)
      | ~ v1_tsep_1(X4,X3)
      | ~ m1_pre_topc(X4,X3)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ r1_tmap_1(X4,sK1,k2_tmap_1(X3,sK1,sK4,X4),X5)
      | r1_tmap_1(X3,sK1,sK4,X5) ) ),
    inference(superposition,[],[f1605,f114])).

fof(f1605,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X0)
      | ~ v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X2)
      | ~ v1_tsep_1(X2,X1)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK4,X2),X3)
      | r1_tmap_1(X1,X0,sK4,X3) ) ),
    inference(resolution,[],[f89,f51])).

fof(f89,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X0)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ v1_tsep_1(X3,X1)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | r1_tmap_1(X1,X0,X2,X5) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ v1_tsep_1(X3,X1)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | X4 != X5
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | r1_tmap_1(X1,X0,X2,X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | ~ v1_tsep_1(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | ~ v1_tsep_1(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & v1_tsep_1(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( X4 = X5
                           => ( r1_tmap_1(X1,X0,X2,X4)
                            <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tmap_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:16:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.45  % (22507)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.46  % (22496)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.48  % (22505)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.49  % (22510)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.49  % (22498)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.49  % (22502)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (22492)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (22494)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.50  % (22489)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (22490)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (22488)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (22499)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (22508)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.52  % (22495)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (22493)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.52  % (22504)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.52  % (22500)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.53  % (22512)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.53  % (22513)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.53  % (22507)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f3102,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(subsumption_resolution,[],[f3101,f2862])).
% 0.21/0.53  fof(f2862,plain,(
% 0.21/0.53    r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),sK5)),
% 0.21/0.53    inference(backward_demodulation,[],[f94,f2861])).
% 0.21/0.53  fof(f2861,plain,(
% 0.21/0.53    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_tmap_1(sK2,sK1,sK4,sK2)),
% 0.21/0.53    inference(forward_demodulation,[],[f2860,f2657])).
% 0.21/0.53  fof(f2657,plain,(
% 0.21/0.53    k2_tmap_1(sK2,sK1,sK4,sK2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,k2_struct_0(sK2))),
% 0.21/0.53    inference(forward_demodulation,[],[f2655,f115])).
% 0.21/0.53  fof(f115,plain,(
% 0.21/0.53    u1_struct_0(sK2) = k2_struct_0(sK2)),
% 0.21/0.53    inference(resolution,[],[f100,f105])).
% 0.21/0.53  fof(f105,plain,(
% 0.21/0.53    l1_pre_topc(sK2)),
% 0.21/0.53    inference(resolution,[],[f102,f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    m1_pre_topc(sK2,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 0.21/0.53    inference(negated_conjecture,[],[f18])).
% 0.21/0.53  fof(f18,conjecture,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tmap_1)).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    ( ! [X1] : (~m1_pre_topc(X1,sK0) | l1_pre_topc(X1)) )),
% 0.21/0.53    inference(resolution,[],[f70,f64])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    l1_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.53  fof(f100,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.53    inference(resolution,[],[f65,f66])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.53  fof(f2655,plain,(
% 0.21/0.53    k2_tmap_1(sK2,sK1,sK4,sK2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(sK2))),
% 0.21/0.53    inference(resolution,[],[f2649,f110])).
% 0.21/0.53  fof(f110,plain,(
% 0.21/0.53    m1_pre_topc(sK2,sK2)),
% 0.21/0.53    inference(resolution,[],[f105,f67])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.21/0.53  fof(f2649,plain,(
% 0.21/0.53    ( ! [X2] : (~m1_pre_topc(X2,sK2) | k2_tmap_1(sK2,sK1,sK4,X2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X2))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f2648,f137])).
% 0.21/0.53  fof(f137,plain,(
% 0.21/0.53    v2_pre_topc(sK2)),
% 0.21/0.53    inference(resolution,[],[f134,f58])).
% 0.21/0.53  % (22503)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.53  fof(f134,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_pre_topc(X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f130,f63])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    v2_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f130,plain,(
% 0.21/0.53    ( ! [X0] : (~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_pre_topc(X0)) )),
% 0.21/0.53    inference(resolution,[],[f81,f64])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_pre_topc(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.21/0.53  fof(f2648,plain,(
% 0.21/0.53    ( ! [X2] : (~v2_pre_topc(sK2) | ~m1_pre_topc(X2,sK2) | k2_tmap_1(sK2,sK1,sK4,X2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X2))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f2647,f403])).
% 0.21/0.53  fof(f403,plain,(
% 0.21/0.53    v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))),
% 0.21/0.53    inference(backward_demodulation,[],[f122,f400])).
% 0.21/0.53  fof(f400,plain,(
% 0.21/0.53    k2_struct_0(sK2) = k2_struct_0(sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f394,f110])).
% 0.21/0.53  fof(f394,plain,(
% 0.21/0.53    ~m1_pre_topc(sK2,sK2) | k2_struct_0(sK2) = k2_struct_0(sK3)),
% 0.21/0.53    inference(resolution,[],[f383,f253])).
% 0.21/0.53  fof(f253,plain,(
% 0.21/0.53    ~m1_pre_topc(sK2,sK3) | k2_struct_0(sK2) = k2_struct_0(sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f195,f252])).
% 0.21/0.53  fof(f252,plain,(
% 0.21/0.53    r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2))),
% 0.21/0.53    inference(subsumption_resolution,[],[f178,f249])).
% 0.21/0.53  fof(f249,plain,(
% 0.21/0.53    m1_pre_topc(sK3,sK2)),
% 0.21/0.53    inference(resolution,[],[f247,f108])).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    m1_pre_topc(sK3,sK3)),
% 0.21/0.53    inference(resolution,[],[f104,f67])).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    l1_pre_topc(sK3)),
% 0.21/0.53    inference(resolution,[],[f102,f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    m1_pre_topc(sK3,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f247,plain,(
% 0.21/0.53    ( ! [X2] : (~m1_pre_topc(X2,sK3) | m1_pre_topc(X2,sK2)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f246,f120])).
% 0.21/0.53  fof(f120,plain,(
% 0.21/0.53    sK3 = g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))),
% 0.21/0.53    inference(backward_demodulation,[],[f54,f115])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    sK3 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f246,plain,(
% 0.21/0.53    ( ! [X2] : (~m1_pre_topc(X2,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) | m1_pre_topc(X2,sK2)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f242,f115])).
% 0.21/0.53  fof(f242,plain,(
% 0.21/0.53    ( ! [X2] : (~m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | m1_pre_topc(X2,sK2)) )),
% 0.21/0.53    inference(resolution,[],[f73,f105])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | m1_pre_topc(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).
% 0.21/0.53  fof(f178,plain,(
% 0.21/0.53    r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) | ~m1_pre_topc(sK3,sK2)),
% 0.21/0.53    inference(superposition,[],[f158,f116])).
% 0.21/0.53  fof(f116,plain,(
% 0.21/0.53    u1_struct_0(sK3) = k2_struct_0(sK3)),
% 0.21/0.53    inference(resolution,[],[f100,f104])).
% 0.21/0.53  fof(f158,plain,(
% 0.21/0.53    ( ! [X2] : (r1_tarski(u1_struct_0(X2),k2_struct_0(sK2)) | ~m1_pre_topc(X2,sK2)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f154,f105])).
% 0.21/0.53  fof(f154,plain,(
% 0.21/0.53    ( ! [X2] : (r1_tarski(u1_struct_0(X2),k2_struct_0(sK2)) | ~m1_pre_topc(X2,sK2) | ~l1_pre_topc(sK2)) )),
% 0.21/0.53    inference(superposition,[],[f71,f115])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).
% 0.21/0.53  fof(f195,plain,(
% 0.21/0.53    ~m1_pre_topc(sK2,sK3) | ~r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) | k2_struct_0(sK2) = k2_struct_0(sK3)),
% 0.21/0.53    inference(resolution,[],[f182,f87])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.53  fof(f182,plain,(
% 0.21/0.53    r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3)),
% 0.21/0.53    inference(superposition,[],[f159,f115])).
% 0.21/0.53  fof(f159,plain,(
% 0.21/0.53    ( ! [X3] : (r1_tarski(u1_struct_0(X3),k2_struct_0(sK3)) | ~m1_pre_topc(X3,sK3)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f155,f104])).
% 0.21/0.53  fof(f155,plain,(
% 0.21/0.53    ( ! [X3] : (r1_tarski(u1_struct_0(X3),k2_struct_0(sK3)) | ~m1_pre_topc(X3,sK3) | ~l1_pre_topc(sK3)) )),
% 0.21/0.53    inference(superposition,[],[f71,f116])).
% 0.21/0.53  fof(f383,plain,(
% 0.21/0.53    ( ! [X2] : (m1_pre_topc(X2,sK3) | ~m1_pre_topc(X2,sK2)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f382,f120])).
% 0.21/0.53  fof(f382,plain,(
% 0.21/0.53    ( ! [X2] : (m1_pre_topc(X2,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) | ~m1_pre_topc(X2,sK2)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f381,f115])).
% 0.21/0.53  fof(f381,plain,(
% 0.21/0.53    ( ! [X2] : (m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~m1_pre_topc(X2,sK2)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f375,f109])).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_pre_topc(X0,sK2) | l1_pre_topc(X0)) )),
% 0.21/0.53    inference(resolution,[],[f105,f70])).
% 0.21/0.53  fof(f375,plain,(
% 0.21/0.53    ( ! [X2] : (~l1_pre_topc(X2) | m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~m1_pre_topc(X2,sK2)) )),
% 0.21/0.53    inference(resolution,[],[f69,f105])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~l1_pre_topc(X0) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).
% 0.21/0.53  fof(f122,plain,(
% 0.21/0.53    v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1))),
% 0.21/0.53    inference(backward_demodulation,[],[f117,f116])).
% 0.21/0.53  fof(f117,plain,(
% 0.21/0.53    v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1))),
% 0.21/0.53    inference(backward_demodulation,[],[f52,f114])).
% 0.21/0.53  fof(f114,plain,(
% 0.21/0.53    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.21/0.53    inference(resolution,[],[f100,f61])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    l1_pre_topc(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f2647,plain,(
% 0.21/0.53    ( ! [X2] : (~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | ~v2_pre_topc(sK2) | ~m1_pre_topc(X2,sK2) | k2_tmap_1(sK2,sK1,sK4,X2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X2))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f2646,f57])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ~v2_struct_0(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f2646,plain,(
% 0.21/0.53    ( ! [X2] : (v2_struct_0(sK2) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | ~v2_pre_topc(sK2) | ~m1_pre_topc(X2,sK2) | k2_tmap_1(sK2,sK1,sK4,X2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X2))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f2645,f105])).
% 0.21/0.53  fof(f2645,plain,(
% 0.21/0.53    ( ! [X2] : (~l1_pre_topc(sK2) | v2_struct_0(sK2) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | ~v2_pre_topc(sK2) | ~m1_pre_topc(X2,sK2) | k2_tmap_1(sK2,sK1,sK4,X2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X2))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f2643,f402])).
% 0.21/0.53  fof(f402,plain,(
% 0.21/0.53    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))))),
% 0.21/0.53    inference(backward_demodulation,[],[f121,f400])).
% 0.21/0.53  fof(f121,plain,(
% 0.21/0.53    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1))))),
% 0.21/0.53    inference(backward_demodulation,[],[f118,f116])).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1))))),
% 0.21/0.53    inference(backward_demodulation,[],[f53,f114])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f2643,plain,(
% 0.21/0.53    ( ! [X2] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))) | ~l1_pre_topc(sK2) | v2_struct_0(sK2) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | ~v2_pre_topc(sK2) | ~m1_pre_topc(X2,sK2) | k2_tmap_1(sK2,sK1,sK4,X2) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X2))) )),
% 0.21/0.53    inference(superposition,[],[f1668,f115])).
% 0.21/0.53  fof(f1668,plain,(
% 0.21/0.53    ( ! [X2,X3] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),k2_struct_0(sK1)))) | ~l1_pre_topc(X2) | v2_struct_0(X2) | ~v1_funct_2(sK4,u1_struct_0(X2),k2_struct_0(sK1)) | ~v2_pre_topc(X2) | ~m1_pre_topc(X3,X2) | k2_tmap_1(X2,sK1,sK4,X3) = k2_partfun1(u1_struct_0(X2),k2_struct_0(sK1),sK4,u1_struct_0(X3))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f1667,f61])).
% 0.21/0.53  fof(f1667,plain,(
% 0.21/0.53    ( ! [X2,X3] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),k2_struct_0(sK1)))) | ~l1_pre_topc(X2) | ~l1_pre_topc(sK1) | v2_struct_0(X2) | ~v1_funct_2(sK4,u1_struct_0(X2),k2_struct_0(sK1)) | ~v2_pre_topc(X2) | ~m1_pre_topc(X3,X2) | k2_tmap_1(X2,sK1,sK4,X3) = k2_partfun1(u1_struct_0(X2),k2_struct_0(sK1),sK4,u1_struct_0(X3))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f1666,f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    v2_pre_topc(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f1666,plain,(
% 0.21/0.53    ( ! [X2,X3] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),k2_struct_0(sK1)))) | ~l1_pre_topc(X2) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X2) | ~v1_funct_2(sK4,u1_struct_0(X2),k2_struct_0(sK1)) | ~v2_pre_topc(X2) | ~m1_pre_topc(X3,X2) | k2_tmap_1(X2,sK1,sK4,X3) = k2_partfun1(u1_struct_0(X2),k2_struct_0(sK1),sK4,u1_struct_0(X3))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f1648,f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ~v2_struct_0(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f1648,plain,(
% 0.21/0.53    ( ! [X2,X3] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),k2_struct_0(sK1)))) | ~l1_pre_topc(X2) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X2) | ~v1_funct_2(sK4,u1_struct_0(X2),k2_struct_0(sK1)) | ~v2_pre_topc(X2) | ~m1_pre_topc(X3,X2) | k2_tmap_1(X2,sK1,sK4,X3) = k2_partfun1(u1_struct_0(X2),k2_struct_0(sK1),sK4,u1_struct_0(X3))) )),
% 0.21/0.53    inference(superposition,[],[f876,f114])).
% 0.21/0.53  fof(f876,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~m1_pre_topc(X2,X0) | k2_tmap_1(X0,X1,sK4,X2) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2))) )),
% 0.21/0.53    inference(resolution,[],[f75,f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    v1_funct_1(sK4)),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  % (22506)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).
% 0.21/0.53  fof(f2860,plain,(
% 0.21/0.53    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,k2_struct_0(sK2))),
% 0.21/0.53    inference(forward_demodulation,[],[f2857,f115])).
% 0.21/0.53  fof(f2857,plain,(
% 0.21/0.53    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(sK2))),
% 0.21/0.53    inference(resolution,[],[f2848,f2125])).
% 0.21/0.53  fof(f2125,plain,(
% 0.21/0.53    m1_pre_topc(sK2,sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f2124,f55])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ~v2_struct_0(sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f2124,plain,(
% 0.21/0.53    m1_pre_topc(sK2,sK3) | v2_struct_0(sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f2119,f249])).
% 0.21/0.53  fof(f2119,plain,(
% 0.21/0.53    ~m1_pre_topc(sK3,sK2) | m1_pre_topc(sK2,sK3) | v2_struct_0(sK3)),
% 0.21/0.53    inference(resolution,[],[f2105,f108])).
% 0.21/0.53  fof(f2105,plain,(
% 0.21/0.53    ( ! [X12] : (~m1_pre_topc(sK3,X12) | ~m1_pre_topc(X12,sK2) | m1_pre_topc(sK2,X12) | v2_struct_0(X12)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f2104,f57])).
% 0.21/0.53  fof(f2104,plain,(
% 0.21/0.53    ( ! [X12] : (v2_struct_0(X12) | ~m1_pre_topc(X12,sK2) | v2_struct_0(sK2) | m1_pre_topc(sK2,X12) | ~m1_pre_topc(sK3,X12)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f2103,f110])).
% 0.21/0.53  fof(f2103,plain,(
% 0.21/0.53    ( ! [X12] : (~m1_pre_topc(sK2,sK2) | v2_struct_0(X12) | ~m1_pre_topc(X12,sK2) | v2_struct_0(sK2) | m1_pre_topc(sK2,X12) | ~m1_pre_topc(sK3,X12)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f2102,f137])).
% 0.21/0.53  fof(f2102,plain,(
% 0.21/0.53    ( ! [X12] : (~v2_pre_topc(sK2) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(X12) | ~m1_pre_topc(X12,sK2) | v2_struct_0(sK2) | m1_pre_topc(sK2,X12) | ~m1_pre_topc(sK3,X12)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f2071,f105])).
% 0.21/0.53  fof(f2071,plain,(
% 0.21/0.53    ( ! [X12] : (~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(X12) | ~m1_pre_topc(X12,sK2) | v2_struct_0(sK2) | m1_pre_topc(sK2,X12) | ~m1_pre_topc(sK3,X12)) )),
% 0.21/0.53    inference(resolution,[],[f2062,f556])).
% 0.21/0.53  fof(f556,plain,(
% 0.21/0.53    v1_tsep_1(sK2,sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f555,f110])).
% 0.21/0.53  fof(f555,plain,(
% 0.21/0.53    ~m1_pre_topc(sK2,sK2) | v1_tsep_1(sK2,sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f553,f142])).
% 0.21/0.53  fof(f142,plain,(
% 0.21/0.53    v3_pre_topc(k2_struct_0(sK2),sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f126,f137])).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    v3_pre_topc(k2_struct_0(sK2),sK2) | ~v2_pre_topc(sK2)),
% 0.21/0.53    inference(resolution,[],[f80,f105])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v3_pre_topc(k2_struct_0(X0),X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).
% 0.21/0.53  fof(f553,plain,(
% 0.21/0.53    ~v3_pre_topc(k2_struct_0(sK2),sK2) | ~m1_pre_topc(sK2,sK2) | v1_tsep_1(sK2,sK2)),
% 0.21/0.53    inference(superposition,[],[f535,f115])).
% 0.21/0.53  fof(f535,plain,(
% 0.21/0.53    ( ! [X2] : (~v3_pre_topc(u1_struct_0(X2),sK2) | ~m1_pre_topc(X2,sK2) | v1_tsep_1(X2,sK2)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f531,f137])).
% 0.21/0.53  fof(f531,plain,(
% 0.21/0.53    ( ! [X2] : (~v2_pre_topc(sK2) | ~m1_pre_topc(X2,sK2) | ~v3_pre_topc(u1_struct_0(X2),sK2) | v1_tsep_1(X2,sK2)) )),
% 0.21/0.53    inference(resolution,[],[f96,f105])).
% 0.21/0.53  % (22491)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | v1_tsep_1(X1,X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f90,f72])).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(u1_struct_0(X1),X0) | v1_tsep_1(X1,X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f84])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | ~v3_pre_topc(X2,X0) | v1_tsep_1(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).
% 0.21/0.53  fof(f2062,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_tsep_1(sK2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(sK2,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | m1_pre_topc(sK2,X1) | ~m1_pre_topc(sK3,X1)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f2055,f70])).
% 0.21/0.53  fof(f2055,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_tsep_1(sK2,X0) | ~m1_pre_topc(sK2,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | m1_pre_topc(sK2,X1) | ~m1_pre_topc(sK3,X1) | ~l1_pre_topc(X1)) )),
% 0.21/0.53    inference(resolution,[],[f781,f406])).
% 0.21/0.53  fof(f406,plain,(
% 0.21/0.53    ( ! [X3] : (r1_tarski(k2_struct_0(sK2),u1_struct_0(X3)) | ~m1_pre_topc(sK3,X3) | ~l1_pre_topc(X3)) )),
% 0.21/0.53    inference(backward_demodulation,[],[f151,f400])).
% 0.21/0.53  fof(f151,plain,(
% 0.21/0.53    ( ! [X3] : (r1_tarski(k2_struct_0(sK3),u1_struct_0(X3)) | ~m1_pre_topc(sK3,X3) | ~l1_pre_topc(X3)) )),
% 0.21/0.53    inference(superposition,[],[f71,f116])).
% 0.21/0.53  fof(f781,plain,(
% 0.21/0.53    ( ! [X4,X5] : (~r1_tarski(k2_struct_0(sK2),u1_struct_0(X4)) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | ~v1_tsep_1(sK2,X5) | ~m1_pre_topc(sK2,X5) | v2_struct_0(X4) | ~m1_pre_topc(X4,X5) | v2_struct_0(X5) | m1_pre_topc(sK2,X4)) )),
% 0.21/0.53    inference(superposition,[],[f79,f115])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0) | m1_pre_topc(X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) => (m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tsep_1)).
% 0.21/0.53  fof(f2848,plain,(
% 0.21/0.53    ( ! [X3] : (~m1_pre_topc(X3,sK3) | k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) = k3_tmap_1(sK0,sK1,sK3,X3,sK4)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f2847,f63])).
% 0.21/0.53  fof(f2847,plain,(
% 0.21/0.53    ( ! [X3] : (~v2_pre_topc(sK0) | ~m1_pre_topc(X3,sK3) | k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) = k3_tmap_1(sK0,sK1,sK3,X3,sK4)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f2846,f62])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ~v2_struct_0(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f2846,plain,(
% 0.21/0.53    ( ! [X3] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_pre_topc(X3,sK3) | k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) = k3_tmap_1(sK0,sK1,sK3,X3,sK4)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f2840,f64])).
% 0.21/0.53  fof(f2840,plain,(
% 0.21/0.53    ( ! [X3] : (~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_pre_topc(X3,sK3) | k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3)) = k3_tmap_1(sK0,sK1,sK3,X3,sK4)) )),
% 0.21/0.53    inference(resolution,[],[f2800,f56])).
% 0.21/0.53  fof(f2800,plain,(
% 0.21/0.53    ( ! [X6,X7] : (~m1_pre_topc(sK3,X6) | ~l1_pre_topc(X6) | v2_struct_0(X6) | ~v2_pre_topc(X6) | ~m1_pre_topc(X7,sK3) | k3_tmap_1(X6,sK1,sK3,X7,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X7))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f2799,f403])).
% 0.21/0.53  fof(f2799,plain,(
% 0.21/0.53    ( ! [X6,X7] : (~l1_pre_topc(X6) | ~m1_pre_topc(sK3,X6) | v2_struct_0(X6) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | ~v2_pre_topc(X6) | ~m1_pre_topc(X7,sK3) | k3_tmap_1(X6,sK1,sK3,X7,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X7))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f2796,f402])).
% 0.21/0.53  fof(f2796,plain,(
% 0.21/0.53    ( ! [X6,X7] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))) | ~l1_pre_topc(X6) | ~m1_pre_topc(sK3,X6) | v2_struct_0(X6) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | ~v2_pre_topc(X6) | ~m1_pre_topc(X7,sK3) | k3_tmap_1(X6,sK1,sK3,X7,sK4) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X7))) )),
% 0.21/0.53    inference(superposition,[],[f2008,f401])).
% 0.21/0.53  fof(f401,plain,(
% 0.21/0.53    u1_struct_0(sK3) = k2_struct_0(sK2)),
% 0.21/0.53    inference(backward_demodulation,[],[f116,f400])).
% 0.21/0.53  fof(f2008,plain,(
% 0.21/0.53    ( ! [X4,X5,X3] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1)))) | ~l1_pre_topc(X4) | ~m1_pre_topc(X3,X4) | v2_struct_0(X4) | ~v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1)) | ~v2_pre_topc(X4) | ~m1_pre_topc(X5,X3) | k3_tmap_1(X4,sK1,X3,X5,sK4) = k2_partfun1(u1_struct_0(X3),k2_struct_0(sK1),sK4,u1_struct_0(X5))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f2007,f61])).
% 0.21/0.53  fof(f2007,plain,(
% 0.21/0.53    ( ! [X4,X5,X3] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1)))) | ~l1_pre_topc(X4) | ~l1_pre_topc(sK1) | ~m1_pre_topc(X3,X4) | v2_struct_0(X4) | ~v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1)) | ~v2_pre_topc(X4) | ~m1_pre_topc(X5,X3) | k3_tmap_1(X4,sK1,X3,X5,sK4) = k2_partfun1(u1_struct_0(X3),k2_struct_0(sK1),sK4,u1_struct_0(X5))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f2006,f60])).
% 0.21/0.53  fof(f2006,plain,(
% 0.21/0.53    ( ! [X4,X5,X3] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1)))) | ~l1_pre_topc(X4) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(X3,X4) | v2_struct_0(X4) | ~v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1)) | ~v2_pre_topc(X4) | ~m1_pre_topc(X5,X3) | k3_tmap_1(X4,sK1,X3,X5,sK4) = k2_partfun1(u1_struct_0(X3),k2_struct_0(sK1),sK4,u1_struct_0(X5))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f2000,f59])).
% 0.21/0.53  fof(f2000,plain,(
% 0.21/0.53    ( ! [X4,X5,X3] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1)))) | ~l1_pre_topc(X4) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(X3,X4) | v2_struct_0(X4) | ~v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1)) | ~v2_pre_topc(X4) | ~m1_pre_topc(X5,X3) | k3_tmap_1(X4,sK1,X3,X5,sK4) = k2_partfun1(u1_struct_0(X3),k2_struct_0(sK1),sK4,u1_struct_0(X5))) )),
% 0.21/0.53    inference(superposition,[],[f1090,f114])).
% 0.21/0.53  fof(f1090,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,sK4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),sK4,u1_struct_0(X3))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f1089,f82])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 0.21/0.53  fof(f1089,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,sK4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),sK4,u1_struct_0(X3))) )),
% 0.21/0.53    inference(resolution,[],[f74,f51])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 0.21/0.53    inference(backward_demodulation,[],[f48,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    sK5 = sK6),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f3101,plain,(
% 0.21/0.53    ~r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),sK5)),
% 0.21/0.53    inference(forward_demodulation,[],[f3100,f2666])).
% 0.21/0.53  fof(f2666,plain,(
% 0.21/0.53    k2_tmap_1(sK2,sK1,sK4,sK2) = k2_tmap_1(sK3,sK1,sK4,sK2)),
% 0.21/0.53    inference(forward_demodulation,[],[f2665,f2657])).
% 0.21/0.53  fof(f2665,plain,(
% 0.21/0.53    k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,k2_struct_0(sK2)) = k2_tmap_1(sK3,sK1,sK4,sK2)),
% 0.21/0.53    inference(forward_demodulation,[],[f2662,f115])).
% 0.21/0.53  fof(f2662,plain,(
% 0.21/0.53    k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,sK4,sK2)),
% 0.21/0.53    inference(resolution,[],[f2654,f2125])).
% 0.21/0.53  fof(f2654,plain,(
% 0.21/0.53    ( ! [X3] : (~m1_pre_topc(X3,sK3) | k2_tmap_1(sK3,sK1,sK4,X3) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f2653,f136])).
% 0.21/0.53  fof(f136,plain,(
% 0.21/0.53    v2_pre_topc(sK3)),
% 0.21/0.53    inference(resolution,[],[f134,f56])).
% 0.21/0.53  fof(f2653,plain,(
% 0.21/0.53    ( ! [X3] : (~v2_pre_topc(sK3) | ~m1_pre_topc(X3,sK3) | k2_tmap_1(sK3,sK1,sK4,X3) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f2652,f403])).
% 0.21/0.53  fof(f2652,plain,(
% 0.21/0.53    ( ! [X3] : (~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | ~v2_pre_topc(sK3) | ~m1_pre_topc(X3,sK3) | k2_tmap_1(sK3,sK1,sK4,X3) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f2651,f55])).
% 0.21/0.53  fof(f2651,plain,(
% 0.21/0.53    ( ! [X3] : (v2_struct_0(sK3) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | ~v2_pre_topc(sK3) | ~m1_pre_topc(X3,sK3) | k2_tmap_1(sK3,sK1,sK4,X3) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f2650,f104])).
% 0.21/0.53  fof(f2650,plain,(
% 0.21/0.53    ( ! [X3] : (~l1_pre_topc(sK3) | v2_struct_0(sK3) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | ~v2_pre_topc(sK3) | ~m1_pre_topc(X3,sK3) | k2_tmap_1(sK3,sK1,sK4,X3) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f2644,f402])).
% 0.21/0.53  fof(f2644,plain,(
% 0.21/0.53    ( ! [X3] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))) | ~l1_pre_topc(sK3) | v2_struct_0(sK3) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | ~v2_pre_topc(sK3) | ~m1_pre_topc(X3,sK3) | k2_tmap_1(sK3,sK1,sK4,X3) = k2_partfun1(k2_struct_0(sK2),k2_struct_0(sK1),sK4,u1_struct_0(X3))) )),
% 0.21/0.53    inference(superposition,[],[f1668,f401])).
% 0.21/0.53  fof(f3100,plain,(
% 0.21/0.53    ~r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK5)),
% 0.21/0.53    inference(subsumption_resolution,[],[f3099,f1495])).
% 0.21/0.53  fof(f1495,plain,(
% 0.21/0.53    v1_tsep_1(sK2,sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f1494,f57])).
% 0.21/0.53  fof(f1494,plain,(
% 0.21/0.53    v2_struct_0(sK2) | v1_tsep_1(sK2,sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f1493,f249])).
% 0.21/0.53  fof(f1493,plain,(
% 0.21/0.53    ~m1_pre_topc(sK3,sK2) | v2_struct_0(sK2) | v1_tsep_1(sK2,sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f1492,f110])).
% 0.21/0.53  fof(f1492,plain,(
% 0.21/0.53    ~m1_pre_topc(sK2,sK2) | ~m1_pre_topc(sK3,sK2) | v2_struct_0(sK2) | v1_tsep_1(sK2,sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f1491,f137])).
% 0.21/0.53  fof(f1491,plain,(
% 0.21/0.53    ~v2_pre_topc(sK2) | ~m1_pre_topc(sK2,sK2) | ~m1_pre_topc(sK3,sK2) | v2_struct_0(sK2) | v1_tsep_1(sK2,sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f1469,f105])).
% 0.21/0.53  fof(f1469,plain,(
% 0.21/0.53    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | ~m1_pre_topc(sK2,sK2) | ~m1_pre_topc(sK3,sK2) | v2_struct_0(sK2) | v1_tsep_1(sK2,sK3)),
% 0.21/0.53    inference(resolution,[],[f1279,f556])).
% 0.21/0.53  fof(f1279,plain,(
% 0.21/0.53    ( ! [X2] : (~v1_tsep_1(sK2,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~m1_pre_topc(sK2,X2) | ~m1_pre_topc(sK3,X2) | v2_struct_0(X2) | v1_tsep_1(sK2,sK3)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f1275,f92])).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.53    inference(equality_resolution,[],[f86])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1275,plain,(
% 0.21/0.53    ( ! [X2] : (~r1_tarski(k2_struct_0(sK2),k2_struct_0(sK2)) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_tsep_1(sK2,X2) | ~m1_pre_topc(sK2,X2) | ~m1_pre_topc(sK3,X2) | v2_struct_0(X2) | v1_tsep_1(sK2,sK3)) )),
% 0.21/0.53    inference(superposition,[],[f669,f115])).
% 0.21/0.53  fof(f669,plain,(
% 0.21/0.53    ( ! [X6,X7] : (~r1_tarski(u1_struct_0(X6),k2_struct_0(sK2)) | ~v2_pre_topc(X7) | ~l1_pre_topc(X7) | ~v1_tsep_1(X6,X7) | ~m1_pre_topc(X6,X7) | ~m1_pre_topc(sK3,X7) | v2_struct_0(X7) | v1_tsep_1(X6,sK3)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f662,f55])).
% 0.21/0.53  fof(f662,plain,(
% 0.21/0.53    ( ! [X6,X7] : (~r1_tarski(u1_struct_0(X6),k2_struct_0(sK2)) | ~v2_pre_topc(X7) | ~l1_pre_topc(X7) | ~v1_tsep_1(X6,X7) | ~m1_pre_topc(X6,X7) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,X7) | v2_struct_0(X7) | v1_tsep_1(X6,sK3)) )),
% 0.21/0.53    inference(superposition,[],[f78,f401])).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0) | v1_tsep_1(X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f37])).
% 0.21/0.53  fof(f3099,plain,(
% 0.21/0.53    ~v1_tsep_1(sK2,sK3) | ~r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK5)),
% 0.21/0.53    inference(subsumption_resolution,[],[f3098,f57])).
% 0.21/0.53  fof(f3098,plain,(
% 0.21/0.53    v2_struct_0(sK2) | ~v1_tsep_1(sK2,sK3) | ~r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK5)),
% 0.21/0.53    inference(subsumption_resolution,[],[f3097,f2125])).
% 0.21/0.53  fof(f3097,plain,(
% 0.21/0.53    ~m1_pre_topc(sK2,sK3) | v2_struct_0(sK2) | ~v1_tsep_1(sK2,sK3) | ~r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK5)),
% 0.21/0.53    inference(subsumption_resolution,[],[f3093,f119])).
% 0.21/0.53  fof(f119,plain,(
% 0.21/0.53    m1_subset_1(sK5,k2_struct_0(sK2))),
% 0.21/0.53    inference(backward_demodulation,[],[f95,f115])).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.21/0.53    inference(forward_demodulation,[],[f46,f47])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f3093,plain,(
% 0.21/0.53    ~m1_subset_1(sK5,k2_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | v2_struct_0(sK2) | ~v1_tsep_1(sK2,sK3) | ~r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK5)),
% 0.21/0.53    inference(superposition,[],[f3090,f115])).
% 0.21/0.53  fof(f3090,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | ~v1_tsep_1(X0,sK3) | ~r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),sK5)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f3089,f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f3089,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_tsep_1(X0,sK3) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),sK5) | r1_tmap_1(sK3,sK1,sK4,sK5)) )),
% 0.21/0.53    inference(resolution,[],[f3060,f119])).
% 0.21/0.53  fof(f3060,plain,(
% 0.21/0.53    ( ! [X6,X7] : (~m1_subset_1(X7,k2_struct_0(sK2)) | ~v1_tsep_1(X6,sK3) | ~m1_pre_topc(X6,sK3) | v2_struct_0(X6) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~r1_tmap_1(X6,sK1,k2_tmap_1(sK3,sK1,sK4,X6),X7) | r1_tmap_1(sK3,sK1,sK4,X7)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f3059,f403])).
% 0.21/0.53  fof(f3059,plain,(
% 0.21/0.53    ( ! [X6,X7] : (~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | v2_struct_0(X6) | ~v1_tsep_1(X6,sK3) | ~m1_pre_topc(X6,sK3) | ~m1_subset_1(X7,k2_struct_0(sK2)) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~r1_tmap_1(X6,sK1,k2_tmap_1(sK3,sK1,sK4,X6),X7) | r1_tmap_1(sK3,sK1,sK4,X7)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f3058,f104])).
% 0.21/0.53  fof(f3058,plain,(
% 0.21/0.53    ( ! [X6,X7] : (~l1_pre_topc(sK3) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | v2_struct_0(X6) | ~v1_tsep_1(X6,sK3) | ~m1_pre_topc(X6,sK3) | ~m1_subset_1(X7,k2_struct_0(sK2)) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~r1_tmap_1(X6,sK1,k2_tmap_1(sK3,sK1,sK4,X6),X7) | r1_tmap_1(sK3,sK1,sK4,X7)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f3057,f136])).
% 0.21/0.53  fof(f3057,plain,(
% 0.21/0.53    ( ! [X6,X7] : (~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | v2_struct_0(X6) | ~v1_tsep_1(X6,sK3) | ~m1_pre_topc(X6,sK3) | ~m1_subset_1(X7,k2_struct_0(sK2)) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~r1_tmap_1(X6,sK1,k2_tmap_1(sK3,sK1,sK4,X6),X7) | r1_tmap_1(sK3,sK1,sK4,X7)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f3056,f55])).
% 0.21/0.53  fof(f3056,plain,(
% 0.21/0.53    ( ! [X6,X7] : (v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | v2_struct_0(X6) | ~v1_tsep_1(X6,sK3) | ~m1_pre_topc(X6,sK3) | ~m1_subset_1(X7,k2_struct_0(sK2)) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~r1_tmap_1(X6,sK1,k2_tmap_1(sK3,sK1,sK4,X6),X7) | r1_tmap_1(sK3,sK1,sK4,X7)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f3050,f402])).
% 0.21/0.53  fof(f3050,plain,(
% 0.21/0.53    ( ! [X6,X7] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))) | v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | v2_struct_0(X6) | ~v1_tsep_1(X6,sK3) | ~m1_pre_topc(X6,sK3) | ~m1_subset_1(X7,k2_struct_0(sK2)) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~r1_tmap_1(X6,sK1,k2_tmap_1(sK3,sK1,sK4,X6),X7) | r1_tmap_1(sK3,sK1,sK4,X7)) )),
% 0.21/0.53    inference(superposition,[],[f2412,f401])).
% 0.21/0.53  fof(f2412,plain,(
% 0.21/0.53    ( ! [X4,X5,X3] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1)))) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1)) | v2_struct_0(X4) | ~v1_tsep_1(X4,X3) | ~m1_pre_topc(X4,X3) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~r1_tmap_1(X4,sK1,k2_tmap_1(X3,sK1,sK4,X4),X5) | r1_tmap_1(X3,sK1,sK4,X5)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f2411,f60])).
% 0.21/0.53  fof(f2411,plain,(
% 0.21/0.53    ( ! [X4,X5,X3] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1)))) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1)) | ~v2_pre_topc(sK1) | v2_struct_0(X4) | ~v1_tsep_1(X4,X3) | ~m1_pre_topc(X4,X3) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~r1_tmap_1(X4,sK1,k2_tmap_1(X3,sK1,sK4,X4),X5) | r1_tmap_1(X3,sK1,sK4,X5)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f2410,f59])).
% 0.21/0.53  fof(f2410,plain,(
% 0.21/0.53    ( ! [X4,X5,X3] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1)))) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | v2_struct_0(sK1) | ~v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1)) | ~v2_pre_topc(sK1) | v2_struct_0(X4) | ~v1_tsep_1(X4,X3) | ~m1_pre_topc(X4,X3) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~r1_tmap_1(X4,sK1,k2_tmap_1(X3,sK1,sK4,X4),X5) | r1_tmap_1(X3,sK1,sK4,X5)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f2392,f61])).
% 0.21/0.53  fof(f2392,plain,(
% 0.21/0.53    ( ! [X4,X5,X3] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1)))) | ~l1_pre_topc(sK1) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | v2_struct_0(sK1) | ~v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1)) | ~v2_pre_topc(sK1) | v2_struct_0(X4) | ~v1_tsep_1(X4,X3) | ~m1_pre_topc(X4,X3) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~r1_tmap_1(X4,sK1,k2_tmap_1(X3,sK1,sK4,X4),X5) | r1_tmap_1(X3,sK1,sK4,X5)) )),
% 0.21/0.53    inference(superposition,[],[f1605,f114])).
% 0.21/0.53  fof(f1605,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0)) | ~v2_pre_topc(X0) | v2_struct_0(X2) | ~v1_tsep_1(X2,X1) | ~m1_pre_topc(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK4,X2),X3) | r1_tmap_1(X1,X0,sK4,X3)) )),
% 0.21/0.53    inference(resolution,[],[f89,f51])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    ( ! [X2,X0,X5,X3,X1] : (~v1_funct_1(X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~v1_tsep_1(X3,X1) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X5)) )),
% 0.21/0.53    inference(equality_resolution,[],[f76])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~v1_tsep_1(X3,X1) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | X4 != X5 | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) | X4 != X5) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tmap_1)).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (22507)------------------------------
% 0.21/0.53  % (22507)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (22507)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (22507)Memory used [KB]: 3198
% 0.21/0.53  % (22507)Time elapsed: 0.119 s
% 0.21/0.53  % (22507)------------------------------
% 0.21/0.53  % (22507)------------------------------
% 0.21/0.53  % (22487)Success in time 0.18 s
%------------------------------------------------------------------------------
