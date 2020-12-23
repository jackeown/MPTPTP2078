%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :  112 (1967 expanded)
%              Number of leaves         :    9 ( 361 expanded)
%              Depth                    :   32
%              Number of atoms          :  332 (13289 expanded)
%              Number of equality atoms :   42 ( 452 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f303,plain,(
    $false ),
    inference(subsumption_resolution,[],[f302,f295])).

fof(f295,plain,(
    ~ r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),sK3) ),
    inference(global_subsumption,[],[f61,f263,f294])).

fof(f294,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),sK3)
    | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) ),
    inference(resolution,[],[f279,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f279,plain,(
    r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) ),
    inference(subsumption_resolution,[],[f278,f32])).

fof(f32,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v4_pre_topc(X2,X0) )
                      & v5_tops_1(X2,X0) )
                    | ( ~ v5_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v4_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v4_pre_topc(X2,X0) )
                      & v5_tops_1(X2,X0) )
                    | ( ~ v5_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v4_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v5_tops_1(X2,X0)
                       => ( v4_tops_1(X2,X0)
                          & v4_pre_topc(X2,X0) ) )
                      & ( ( v4_tops_1(X3,X1)
                          & v4_pre_topc(X3,X1) )
                       => v5_tops_1(X3,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v5_tops_1(X2,X0)
                     => ( v4_tops_1(X2,X0)
                        & v4_pre_topc(X2,X0) ) )
                    & ( ( v4_tops_1(X3,X1)
                        & v4_pre_topc(X3,X1) )
                     => v5_tops_1(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tops_1)).

fof(f278,plain,
    ( r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3)))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f275,f30])).

fof(f30,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f12])).

fof(f275,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f264,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tops_1)).

fof(f264,plain,(
    v4_tops_1(sK3,sK1) ),
    inference(subsumption_resolution,[],[f260,f251])).

fof(f251,plain,(
    v4_tops_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f247,f69])).

fof(f69,plain,(
    r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(subsumption_resolution,[],[f63,f34])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f63,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(resolution,[],[f31,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f247,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | v4_tops_1(sK2,sK0) ),
    inference(backward_demodulation,[],[f246,f241])).

fof(f241,plain,(
    sK2 = k2_pre_topc(sK0,sK2) ),
    inference(backward_demodulation,[],[f103,f238])).

fof(f238,plain,(
    sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f237,f34])).

fof(f237,plain,
    ( sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f236,f31])).

fof(f236,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f235,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v5_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tops_1)).

fof(f235,plain,(
    v5_tops_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f233,f74])).

fof(f74,plain,
    ( sK2 != k2_pre_topc(sK0,k1_tops_1(sK0,sK2))
    | v5_tops_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f67,f34])).

fof(f67,plain,
    ( ~ l1_pre_topc(sK0)
    | sK2 != k2_pre_topc(sK0,k1_tops_1(sK0,sK2))
    | v5_tops_1(sK2,sK0) ),
    inference(resolution,[],[f31,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1
      | v5_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f233,plain,
    ( sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2))
    | v5_tops_1(sK2,sK0) ),
    inference(resolution,[],[f231,f27])).

fof(f27,plain,
    ( ~ v5_tops_1(sK3,sK1)
    | v5_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f231,plain,
    ( v5_tops_1(sK3,sK1)
    | sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) ),
    inference(trivial_inequality_removal,[],[f223])).

fof(f223,plain,
    ( sK3 != sK3
    | v5_tops_1(sK3,sK1)
    | sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) ),
    inference(superposition,[],[f61,f220])).

fof(f220,plain,
    ( sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3))
    | sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) ),
    inference(duplicate_literal_removal,[],[f218])).

fof(f218,plain,
    ( sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2))
    | sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2))
    | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) ),
    inference(resolution,[],[f160,f141])).

fof(f141,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),sK3)
    | sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2))
    | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) ),
    inference(resolution,[],[f117,f46])).

fof(f117,plain,
    ( r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3)))
    | sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f116,f32])).

fof(f116,plain,
    ( sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2))
    | r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3)))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f113,f30])).

fof(f113,plain,
    ( sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f79,f38])).

fof(f79,plain,
    ( v4_tops_1(sK3,sK1)
    | sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f78,f34])).

fof(f78,plain,
    ( v4_tops_1(sK3,sK1)
    | sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f77,f31])).

% (4913)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% (4906)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
fof(f77,plain,
    ( v4_tops_1(sK3,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f28,f36])).

fof(f28,plain,
    ( v5_tops_1(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f160,plain,
    ( r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),sK3)
    | sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f159,f34])).

fof(f159,plain,
    ( r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),sK3)
    | sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f158,f31])).

fof(f158,plain,
    ( r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f121,f36])).

fof(f121,plain,
    ( v5_tops_1(sK2,sK0)
    | r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),sK3) ),
    inference(subsumption_resolution,[],[f119,f57])).

fof(f57,plain,(
    r1_tarski(k1_tops_1(sK1,sK3),sK3) ),
    inference(subsumption_resolution,[],[f51,f32])).

fof(f51,plain,
    ( ~ l1_pre_topc(sK1)
    | r1_tarski(k1_tops_1(sK1,sK3),sK3) ),
    inference(resolution,[],[f30,f43])).

fof(f119,plain,
    ( v5_tops_1(sK2,sK0)
    | ~ r1_tarski(k1_tops_1(sK1,sK3),sK3)
    | r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),sK3) ),
    inference(resolution,[],[f83,f58])).

fof(f58,plain,(
    m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f52,f32])).

fof(f52,plain,
    ( ~ l1_pre_topc(sK1)
    | m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(resolution,[],[f30,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f83,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | v5_tops_1(sK2,sK0)
      | ~ r1_tarski(X0,sK3)
      | r1_tarski(k2_pre_topc(sK1,X0),sK3) ) ),
    inference(subsumption_resolution,[],[f82,f32])).

fof(f82,plain,(
    ! [X0] :
      ( v5_tops_1(sK2,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_pre_topc(sK1)
      | ~ r1_tarski(X0,sK3)
      | r1_tarski(k2_pre_topc(sK1,X0),sK3) ) ),
    inference(subsumption_resolution,[],[f81,f30])).

fof(f81,plain,(
    ! [X0] :
      ( v5_tops_1(sK2,sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_pre_topc(sK1)
      | ~ r1_tarski(X0,sK3)
      | r1_tarski(k2_pre_topc(sK1,X0),sK3) ) ),
    inference(resolution,[],[f29,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ r1_tarski(X2,X1)
      | r1_tarski(k2_pre_topc(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X2),X1)
              | ~ r1_tarski(X2,X1)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X2),X1)
              | ~ r1_tarski(X2,X1)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X2,X1)
                  & v4_pre_topc(X1,X0) )
               => r1_tarski(k2_pre_topc(X0,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_1)).

fof(f29,plain,
    ( v4_pre_topc(sK3,sK1)
    | v5_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f103,plain,(
    k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f97,f34])).

fof(f97,plain,
    ( ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) ),
    inference(resolution,[],[f70,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

fof(f70,plain,(
    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f64,f34])).

fof(f64,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f31,f42])).

fof(f246,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
    | v4_tops_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f239,f49])).

fof(f49,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f239,plain,
    ( ~ r1_tarski(sK2,sK2)
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
    | v4_tops_1(sK2,sK0) ),
    inference(backward_demodulation,[],[f73,f238])).

fof(f73,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
    | ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | v4_tops_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f66,f34])).

fof(f66,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2)
    | ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | v4_tops_1(sK2,sK0) ),
    inference(resolution,[],[f31,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | v4_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f260,plain,
    ( v4_tops_1(sK3,sK1)
    | ~ v4_tops_1(sK2,sK0) ),
    inference(resolution,[],[f249,f25])).

fof(f25,plain,
    ( ~ v4_pre_topc(sK2,sK0)
    | v4_tops_1(sK3,sK1)
    | ~ v4_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f249,plain,(
    v4_pre_topc(sK2,sK0) ),
    inference(backward_demodulation,[],[f72,f241])).

fof(f72,plain,(
    v4_pre_topc(k2_pre_topc(sK0,sK2),sK0) ),
    inference(subsumption_resolution,[],[f71,f33])).

fof(f33,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f71,plain,
    ( ~ v2_pre_topc(sK0)
    | v4_pre_topc(k2_pre_topc(sK0,sK2),sK0) ),
    inference(subsumption_resolution,[],[f65,f34])).

fof(f65,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v4_pre_topc(k2_pre_topc(sK0,sK2),sK0) ),
    inference(resolution,[],[f31,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f263,plain,(
    ~ v5_tops_1(sK3,sK1) ),
    inference(subsumption_resolution,[],[f259,f251])).

fof(f259,plain,
    ( ~ v5_tops_1(sK3,sK1)
    | ~ v4_tops_1(sK2,sK0) ),
    inference(resolution,[],[f249,f26])).

fof(f26,plain,
    ( ~ v4_pre_topc(sK2,sK0)
    | ~ v5_tops_1(sK3,sK1)
    | ~ v4_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f61,plain,
    ( sK3 != k2_pre_topc(sK1,k1_tops_1(sK1,sK3))
    | v5_tops_1(sK3,sK1) ),
    inference(subsumption_resolution,[],[f55,f32])).

fof(f55,plain,
    ( ~ l1_pre_topc(sK1)
    | sK3 != k2_pre_topc(sK1,k1_tops_1(sK1,sK3))
    | v5_tops_1(sK3,sK1) ),
    inference(resolution,[],[f30,f35])).

fof(f302,plain,(
    r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),sK3) ),
    inference(subsumption_resolution,[],[f297,f57])).

fof(f297,plain,
    ( ~ r1_tarski(k1_tops_1(sK1,sK3),sK3)
    | r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),sK3) ),
    inference(resolution,[],[f282,f58])).

fof(f282,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r1_tarski(X0,sK3)
      | r1_tarski(k2_pre_topc(sK1,X0),sK3) ) ),
    inference(subsumption_resolution,[],[f281,f32])).

fof(f281,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_pre_topc(sK1)
      | ~ r1_tarski(X0,sK3)
      | r1_tarski(k2_pre_topc(sK1,X0),sK3) ) ),
    inference(subsumption_resolution,[],[f280,f30])).

fof(f280,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_pre_topc(sK1)
      | ~ r1_tarski(X0,sK3)
      | r1_tarski(k2_pre_topc(sK1,X0),sK3) ) ),
    inference(resolution,[],[f265,f41])).

fof(f265,plain,(
    v4_pre_topc(sK3,sK1) ),
    inference(subsumption_resolution,[],[f261,f251])).

fof(f261,plain,
    ( v4_pre_topc(sK3,sK1)
    | ~ v4_tops_1(sK2,sK0) ),
    inference(resolution,[],[f249,f24])).

fof(f24,plain,
    ( ~ v4_pre_topc(sK2,sK0)
    | v4_pre_topc(sK3,sK1)
    | ~ v4_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:48:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.54  % (4901)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.54  % (4904)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.54  % (4902)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.55  % (4904)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % (4900)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.55  % (4922)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.55  % (4903)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.55  % (4914)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.55  % (4899)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.55  % (4912)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (4920)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f303,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(subsumption_resolution,[],[f302,f295])).
% 0.21/0.56  fof(f295,plain,(
% 0.21/0.56    ~r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),sK3)),
% 0.21/0.56    inference(global_subsumption,[],[f61,f263,f294])).
% 0.21/0.56  fof(f294,plain,(
% 0.21/0.56    ~r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),sK3) | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3))),
% 0.21/0.56    inference(resolution,[],[f279,f46])).
% 0.21/0.56  fof(f46,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.56  fof(f279,plain,(
% 0.21/0.56    r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3)))),
% 0.21/0.56    inference(subsumption_resolution,[],[f278,f32])).
% 0.21/0.56  fof(f32,plain,(
% 0.21/0.56    l1_pre_topc(sK1)),
% 0.21/0.56    inference(cnf_transformation,[],[f12])).
% 0.21/0.56  fof(f12,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.56    inference(flattening,[],[f11])).
% 0.21/0.56  fof(f11,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(X3,X1) & (v4_tops_1(X3,X1) & v4_pre_topc(X3,X1)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f10])).
% 0.21/0.56  fof(f10,negated_conjecture,(
% 0.21/0.56    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v5_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v4_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v4_pre_topc(X3,X1)) => v5_tops_1(X3,X1)))))))),
% 0.21/0.56    inference(negated_conjecture,[],[f9])).
% 0.21/0.56  fof(f9,conjecture,(
% 0.21/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v5_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v4_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v4_pre_topc(X3,X1)) => v5_tops_1(X3,X1)))))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tops_1)).
% 0.21/0.56  fof(f278,plain,(
% 0.21/0.56    r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) | ~l1_pre_topc(sK1)),
% 0.21/0.56    inference(subsumption_resolution,[],[f275,f30])).
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.56    inference(cnf_transformation,[],[f12])).
% 0.21/0.56  fof(f275,plain,(
% 0.21/0.56    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) | ~l1_pre_topc(sK1)),
% 0.21/0.56    inference(resolution,[],[f264,f38])).
% 0.21/0.56  fof(f38,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~l1_pre_topc(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f14])).
% 0.21/0.56  fof(f14,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : ((v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tops_1)).
% 0.21/0.56  fof(f264,plain,(
% 0.21/0.56    v4_tops_1(sK3,sK1)),
% 0.21/0.56    inference(subsumption_resolution,[],[f260,f251])).
% 0.21/0.56  fof(f251,plain,(
% 0.21/0.56    v4_tops_1(sK2,sK0)),
% 0.21/0.56    inference(subsumption_resolution,[],[f247,f69])).
% 0.21/0.56  fof(f69,plain,(
% 0.21/0.56    r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 0.21/0.56    inference(subsumption_resolution,[],[f63,f34])).
% 0.21/0.56  fof(f34,plain,(
% 0.21/0.56    l1_pre_topc(sK0)),
% 0.21/0.56    inference(cnf_transformation,[],[f12])).
% 0.21/0.56  fof(f63,plain,(
% 0.21/0.56    ~l1_pre_topc(sK0) | r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 0.21/0.56    inference(resolution,[],[f31,f43])).
% 0.21/0.56  fof(f43,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f21])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,axiom,(
% 0.21/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 0.21/0.56  fof(f31,plain,(
% 0.21/0.56    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.56    inference(cnf_transformation,[],[f12])).
% 0.21/0.56  fof(f247,plain,(
% 0.21/0.56    ~r1_tarski(k1_tops_1(sK0,sK2),sK2) | v4_tops_1(sK2,sK0)),
% 0.21/0.56    inference(backward_demodulation,[],[f246,f241])).
% 0.21/0.56  fof(f241,plain,(
% 0.21/0.56    sK2 = k2_pre_topc(sK0,sK2)),
% 0.21/0.56    inference(backward_demodulation,[],[f103,f238])).
% 0.21/0.56  fof(f238,plain,(
% 0.21/0.56    sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),
% 0.21/0.56    inference(subsumption_resolution,[],[f237,f34])).
% 0.21/0.56  fof(f237,plain,(
% 0.21/0.56    sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) | ~l1_pre_topc(sK0)),
% 0.21/0.56    inference(subsumption_resolution,[],[f236,f31])).
% 0.21/0.56  fof(f236,plain,(
% 0.21/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) | ~l1_pre_topc(sK0)),
% 0.21/0.56    inference(resolution,[],[f235,f36])).
% 0.21/0.56  fof(f36,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~v5_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~l1_pre_topc(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f13])).
% 0.21/0.56  fof(f13,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : ((v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tops_1)).
% 0.21/0.56  fof(f235,plain,(
% 0.21/0.56    v5_tops_1(sK2,sK0)),
% 0.21/0.56    inference(subsumption_resolution,[],[f233,f74])).
% 0.21/0.56  fof(f74,plain,(
% 0.21/0.56    sK2 != k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) | v5_tops_1(sK2,sK0)),
% 0.21/0.56    inference(subsumption_resolution,[],[f67,f34])).
% 0.21/0.56  fof(f67,plain,(
% 0.21/0.56    ~l1_pre_topc(sK0) | sK2 != k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) | v5_tops_1(sK2,sK0)),
% 0.21/0.56    inference(resolution,[],[f31,f35])).
% 0.21/0.56  fof(f35,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 | v5_tops_1(X1,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f13])).
% 0.21/0.56  fof(f233,plain,(
% 0.21/0.56    sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) | v5_tops_1(sK2,sK0)),
% 0.21/0.56    inference(resolution,[],[f231,f27])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    ~v5_tops_1(sK3,sK1) | v5_tops_1(sK2,sK0)),
% 0.21/0.56    inference(cnf_transformation,[],[f12])).
% 0.21/0.56  fof(f231,plain,(
% 0.21/0.56    v5_tops_1(sK3,sK1) | sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),
% 0.21/0.56    inference(trivial_inequality_removal,[],[f223])).
% 0.21/0.56  fof(f223,plain,(
% 0.21/0.56    sK3 != sK3 | v5_tops_1(sK3,sK1) | sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),
% 0.21/0.56    inference(superposition,[],[f61,f220])).
% 0.21/0.56  fof(f220,plain,(
% 0.21/0.56    sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) | sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f218])).
% 0.21/0.56  fof(f218,plain,(
% 0.21/0.56    sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) | sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3))),
% 0.21/0.56    inference(resolution,[],[f160,f141])).
% 0.21/0.56  fof(f141,plain,(
% 0.21/0.56    ~r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),sK3) | sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3))),
% 0.21/0.56    inference(resolution,[],[f117,f46])).
% 0.21/0.56  fof(f117,plain,(
% 0.21/0.56    r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) | sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),
% 0.21/0.56    inference(subsumption_resolution,[],[f116,f32])).
% 0.21/0.56  fof(f116,plain,(
% 0.21/0.56    sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) | r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) | ~l1_pre_topc(sK1)),
% 0.21/0.56    inference(subsumption_resolution,[],[f113,f30])).
% 0.21/0.56  fof(f113,plain,(
% 0.21/0.56    sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) | ~l1_pre_topc(sK1)),
% 0.21/0.56    inference(resolution,[],[f79,f38])).
% 0.21/0.56  fof(f79,plain,(
% 0.21/0.56    v4_tops_1(sK3,sK1) | sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),
% 0.21/0.56    inference(subsumption_resolution,[],[f78,f34])).
% 0.21/0.56  fof(f78,plain,(
% 0.21/0.56    v4_tops_1(sK3,sK1) | sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) | ~l1_pre_topc(sK0)),
% 0.21/0.56    inference(subsumption_resolution,[],[f77,f31])).
% 0.21/0.56  % (4913)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.49/0.56  % (4906)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.49/0.56  fof(f77,plain,(
% 1.49/0.56    v4_tops_1(sK3,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) | ~l1_pre_topc(sK0)),
% 1.49/0.56    inference(resolution,[],[f28,f36])).
% 1.49/0.56  fof(f28,plain,(
% 1.49/0.56    v5_tops_1(sK2,sK0) | v4_tops_1(sK3,sK1)),
% 1.49/0.56    inference(cnf_transformation,[],[f12])).
% 1.49/0.56  fof(f160,plain,(
% 1.49/0.56    r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),sK3) | sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),
% 1.49/0.56    inference(subsumption_resolution,[],[f159,f34])).
% 1.49/0.56  fof(f159,plain,(
% 1.49/0.56    r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),sK3) | sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) | ~l1_pre_topc(sK0)),
% 1.49/0.56    inference(subsumption_resolution,[],[f158,f31])).
% 1.49/0.56  fof(f158,plain,(
% 1.49/0.56    r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) | ~l1_pre_topc(sK0)),
% 1.49/0.56    inference(resolution,[],[f121,f36])).
% 1.49/0.56  fof(f121,plain,(
% 1.49/0.56    v5_tops_1(sK2,sK0) | r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),sK3)),
% 1.49/0.56    inference(subsumption_resolution,[],[f119,f57])).
% 1.49/0.56  fof(f57,plain,(
% 1.49/0.56    r1_tarski(k1_tops_1(sK1,sK3),sK3)),
% 1.49/0.56    inference(subsumption_resolution,[],[f51,f32])).
% 1.49/0.56  fof(f51,plain,(
% 1.49/0.56    ~l1_pre_topc(sK1) | r1_tarski(k1_tops_1(sK1,sK3),sK3)),
% 1.49/0.56    inference(resolution,[],[f30,f43])).
% 1.49/0.56  fof(f119,plain,(
% 1.49/0.56    v5_tops_1(sK2,sK0) | ~r1_tarski(k1_tops_1(sK1,sK3),sK3) | r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),sK3)),
% 1.49/0.56    inference(resolution,[],[f83,f58])).
% 1.49/0.56  fof(f58,plain,(
% 1.49/0.56    m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.49/0.56    inference(subsumption_resolution,[],[f52,f32])).
% 1.49/0.56  fof(f52,plain,(
% 1.49/0.56    ~l1_pre_topc(sK1) | m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.49/0.56    inference(resolution,[],[f30,f42])).
% 1.49/0.56  fof(f42,plain,(
% 1.49/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.49/0.56    inference(cnf_transformation,[],[f20])).
% 1.49/0.56  fof(f20,plain,(
% 1.49/0.56    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.49/0.56    inference(flattening,[],[f19])).
% 1.49/0.56  fof(f19,plain,(
% 1.49/0.56    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.49/0.56    inference(ennf_transformation,[],[f5])).
% 1.49/0.56  fof(f5,axiom,(
% 1.49/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.49/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).
% 1.49/0.56  fof(f83,plain,(
% 1.49/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | v5_tops_1(sK2,sK0) | ~r1_tarski(X0,sK3) | r1_tarski(k2_pre_topc(sK1,X0),sK3)) )),
% 1.49/0.56    inference(subsumption_resolution,[],[f82,f32])).
% 1.49/0.56  fof(f82,plain,(
% 1.49/0.56    ( ! [X0] : (v5_tops_1(sK2,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~r1_tarski(X0,sK3) | r1_tarski(k2_pre_topc(sK1,X0),sK3)) )),
% 1.49/0.56    inference(subsumption_resolution,[],[f81,f30])).
% 1.49/0.56  fof(f81,plain,(
% 1.49/0.56    ( ! [X0] : (v5_tops_1(sK2,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~r1_tarski(X0,sK3) | r1_tarski(k2_pre_topc(sK1,X0),sK3)) )),
% 1.49/0.56    inference(resolution,[],[f29,f41])).
% 1.49/0.56  fof(f41,plain,(
% 1.49/0.56    ( ! [X2,X0,X1] : (~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~r1_tarski(X2,X1) | r1_tarski(k2_pre_topc(X0,X2),X1)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f18])).
% 1.49/0.56  fof(f18,plain,(
% 1.49/0.56    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X2),X1) | ~r1_tarski(X2,X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.49/0.56    inference(flattening,[],[f17])).
% 1.49/0.56  fof(f17,plain,(
% 1.49/0.56    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X2),X1) | (~r1_tarski(X2,X1) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.49/0.56    inference(ennf_transformation,[],[f7])).
% 1.49/0.56  fof(f7,axiom,(
% 1.49/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X2,X1) & v4_pre_topc(X1,X0)) => r1_tarski(k2_pre_topc(X0,X2),X1)))))),
% 1.49/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_1)).
% 1.49/0.56  fof(f29,plain,(
% 1.49/0.56    v4_pre_topc(sK3,sK1) | v5_tops_1(sK2,sK0)),
% 1.49/0.56    inference(cnf_transformation,[],[f12])).
% 1.49/0.56  fof(f103,plain,(
% 1.49/0.56    k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))),
% 1.49/0.56    inference(subsumption_resolution,[],[f97,f34])).
% 1.49/0.56  fof(f97,plain,(
% 1.49/0.56    ~l1_pre_topc(sK0) | k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))),
% 1.49/0.56    inference(resolution,[],[f70,f47])).
% 1.49/0.56  fof(f47,plain,(
% 1.49/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))) )),
% 1.49/0.56    inference(cnf_transformation,[],[f23])).
% 1.49/0.56  fof(f23,plain,(
% 1.49/0.56    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.49/0.56    inference(flattening,[],[f22])).
% 1.49/0.56  fof(f22,plain,(
% 1.49/0.56    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.49/0.56    inference(ennf_transformation,[],[f2])).
% 1.49/0.56  fof(f2,axiom,(
% 1.49/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)))),
% 1.49/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).
% 1.49/0.56  fof(f70,plain,(
% 1.49/0.56    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.49/0.56    inference(subsumption_resolution,[],[f64,f34])).
% 1.49/0.56  fof(f64,plain,(
% 1.49/0.56    ~l1_pre_topc(sK0) | m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.49/0.56    inference(resolution,[],[f31,f42])).
% 1.49/0.56  fof(f246,plain,(
% 1.49/0.56    ~r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2) | v4_tops_1(sK2,sK0)),
% 1.49/0.56    inference(subsumption_resolution,[],[f239,f49])).
% 1.49/0.56  fof(f49,plain,(
% 1.49/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.49/0.56    inference(equality_resolution,[],[f44])).
% 1.49/0.56  fof(f44,plain,(
% 1.49/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.49/0.56    inference(cnf_transformation,[],[f1])).
% 1.49/0.56  fof(f239,plain,(
% 1.49/0.56    ~r1_tarski(sK2,sK2) | ~r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2) | v4_tops_1(sK2,sK0)),
% 1.49/0.56    inference(backward_demodulation,[],[f73,f238])).
% 1.49/0.56  fof(f73,plain,(
% 1.49/0.56    ~r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2) | ~r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) | v4_tops_1(sK2,sK0)),
% 1.49/0.56    inference(subsumption_resolution,[],[f66,f34])).
% 1.49/0.56  fof(f66,plain,(
% 1.49/0.56    ~l1_pre_topc(sK0) | ~r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK2) | ~r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) | v4_tops_1(sK2,sK0)),
% 1.49/0.56    inference(resolution,[],[f31,f39])).
% 1.49/0.56  fof(f39,plain,(
% 1.49/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | v4_tops_1(X1,X0)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f14])).
% 1.49/0.56  fof(f260,plain,(
% 1.49/0.56    v4_tops_1(sK3,sK1) | ~v4_tops_1(sK2,sK0)),
% 1.49/0.56    inference(resolution,[],[f249,f25])).
% 1.49/0.56  fof(f25,plain,(
% 1.49/0.56    ~v4_pre_topc(sK2,sK0) | v4_tops_1(sK3,sK1) | ~v4_tops_1(sK2,sK0)),
% 1.49/0.56    inference(cnf_transformation,[],[f12])).
% 1.49/0.56  fof(f249,plain,(
% 1.49/0.56    v4_pre_topc(sK2,sK0)),
% 1.49/0.56    inference(backward_demodulation,[],[f72,f241])).
% 1.49/0.56  fof(f72,plain,(
% 1.49/0.56    v4_pre_topc(k2_pre_topc(sK0,sK2),sK0)),
% 1.49/0.56    inference(subsumption_resolution,[],[f71,f33])).
% 1.49/0.56  fof(f33,plain,(
% 1.49/0.56    v2_pre_topc(sK0)),
% 1.49/0.56    inference(cnf_transformation,[],[f12])).
% 1.49/0.57  fof(f71,plain,(
% 1.49/0.57    ~v2_pre_topc(sK0) | v4_pre_topc(k2_pre_topc(sK0,sK2),sK0)),
% 1.49/0.57    inference(subsumption_resolution,[],[f65,f34])).
% 1.49/0.57  fof(f65,plain,(
% 1.49/0.57    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v4_pre_topc(k2_pre_topc(sK0,sK2),sK0)),
% 1.49/0.57    inference(resolution,[],[f31,f40])).
% 1.49/0.57  fof(f40,plain,(
% 1.49/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v4_pre_topc(k2_pre_topc(X0,X1),X0)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f16])).
% 1.49/0.57  fof(f16,plain,(
% 1.49/0.57    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.49/0.57    inference(flattening,[],[f15])).
% 1.49/0.57  fof(f15,plain,(
% 1.49/0.57    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.49/0.57    inference(ennf_transformation,[],[f6])).
% 1.49/0.57  fof(f6,axiom,(
% 1.49/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).
% 1.49/0.57  fof(f263,plain,(
% 1.49/0.57    ~v5_tops_1(sK3,sK1)),
% 1.49/0.57    inference(subsumption_resolution,[],[f259,f251])).
% 1.49/0.57  fof(f259,plain,(
% 1.49/0.57    ~v5_tops_1(sK3,sK1) | ~v4_tops_1(sK2,sK0)),
% 1.49/0.57    inference(resolution,[],[f249,f26])).
% 1.49/0.57  fof(f26,plain,(
% 1.49/0.57    ~v4_pre_topc(sK2,sK0) | ~v5_tops_1(sK3,sK1) | ~v4_tops_1(sK2,sK0)),
% 1.49/0.57    inference(cnf_transformation,[],[f12])).
% 1.49/0.57  fof(f61,plain,(
% 1.49/0.57    sK3 != k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) | v5_tops_1(sK3,sK1)),
% 1.49/0.57    inference(subsumption_resolution,[],[f55,f32])).
% 1.49/0.57  fof(f55,plain,(
% 1.49/0.57    ~l1_pre_topc(sK1) | sK3 != k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) | v5_tops_1(sK3,sK1)),
% 1.49/0.57    inference(resolution,[],[f30,f35])).
% 1.49/0.57  fof(f302,plain,(
% 1.49/0.57    r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),sK3)),
% 1.49/0.57    inference(subsumption_resolution,[],[f297,f57])).
% 1.49/0.57  fof(f297,plain,(
% 1.49/0.57    ~r1_tarski(k1_tops_1(sK1,sK3),sK3) | r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),sK3)),
% 1.49/0.57    inference(resolution,[],[f282,f58])).
% 1.49/0.57  fof(f282,plain,(
% 1.49/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_tarski(X0,sK3) | r1_tarski(k2_pre_topc(sK1,X0),sK3)) )),
% 1.49/0.57    inference(subsumption_resolution,[],[f281,f32])).
% 1.49/0.57  fof(f281,plain,(
% 1.49/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~r1_tarski(X0,sK3) | r1_tarski(k2_pre_topc(sK1,X0),sK3)) )),
% 1.49/0.57    inference(subsumption_resolution,[],[f280,f30])).
% 1.49/0.57  fof(f280,plain,(
% 1.49/0.57    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~r1_tarski(X0,sK3) | r1_tarski(k2_pre_topc(sK1,X0),sK3)) )),
% 1.49/0.57    inference(resolution,[],[f265,f41])).
% 1.49/0.57  fof(f265,plain,(
% 1.49/0.57    v4_pre_topc(sK3,sK1)),
% 1.49/0.57    inference(subsumption_resolution,[],[f261,f251])).
% 1.49/0.57  fof(f261,plain,(
% 1.49/0.57    v4_pre_topc(sK3,sK1) | ~v4_tops_1(sK2,sK0)),
% 1.49/0.57    inference(resolution,[],[f249,f24])).
% 1.49/0.57  fof(f24,plain,(
% 1.49/0.57    ~v4_pre_topc(sK2,sK0) | v4_pre_topc(sK3,sK1) | ~v4_tops_1(sK2,sK0)),
% 1.49/0.57    inference(cnf_transformation,[],[f12])).
% 1.49/0.57  % SZS output end Proof for theBenchmark
% 1.49/0.57  % (4904)------------------------------
% 1.49/0.57  % (4904)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.57  % (4904)Termination reason: Refutation
% 1.49/0.57  
% 1.49/0.57  % (4904)Memory used [KB]: 6396
% 1.49/0.57  % (4904)Time elapsed: 0.126 s
% 1.49/0.57  % (4904)------------------------------
% 1.49/0.57  % (4904)------------------------------
% 1.49/0.57  % (4916)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.49/0.57  % (4915)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.49/0.57  % (4898)Success in time 0.201 s
%------------------------------------------------------------------------------
