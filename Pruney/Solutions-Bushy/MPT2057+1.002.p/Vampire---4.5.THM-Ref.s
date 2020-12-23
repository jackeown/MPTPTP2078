%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT2057+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:06 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 601 expanded)
%              Number of leaves         :   10 ( 109 expanded)
%              Depth                    :   26
%              Number of atoms          :  392 (4155 expanded)
%              Number of equality atoms :   31 (  73 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f140,plain,(
    $false ),
    inference(subsumption_resolution,[],[f127,f36])).

fof(f36,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f127,plain,(
    ~ v1_xboole_0(o_0_0_xboole_0) ),
    inference(backward_demodulation,[],[f28,f124])).

fof(f124,plain,(
    o_0_0_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f123,f34])).

fof(f34,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,X1)
              <~> r1_waybel_0(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,X1)
              <~> r1_waybel_0(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & ~ v1_xboole_0(X2) )
               => ( r2_hidden(X2,X1)
                <=> r1_waybel_0(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & ~ v1_xboole_0(X2) )
             => ( r2_hidden(X2,X1)
              <=> r1_waybel_0(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_yellow19)).

fof(f123,plain,
    ( o_0_0_xboole_0 = sK2
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f121,f35])).

fof(f35,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f121,plain,
    ( o_0_0_xboole_0 = sK2
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f117,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f117,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | o_0_0_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f115,f106])).

fof(f106,plain,
    ( r2_hidden(sK2,sK1)
    | v1_xboole_0(k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f105,f100])).

fof(f100,plain,
    ( ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v1_xboole_0(k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f99,f32])).

fof(f32,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f99,plain,
    ( ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f98,f31])).

fof(f31,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f98,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f97,f30])).

fof(f30,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f97,plain,
    ( v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f72,f33])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f14])).

fof(f72,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),X2)) ) ),
    inference(subsumption_resolution,[],[f71,f34])).

fof(f71,plain,(
    ! [X2] :
      ( v1_xboole_0(k2_struct_0(sK0))
      | v2_struct_0(sK0)
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),X2)) ) ),
    inference(subsumption_resolution,[],[f66,f35])).

fof(f66,plain,(
    ! [X2] :
      ( ~ l1_struct_0(sK0)
      | v1_xboole_0(k2_struct_0(sK0))
      | v2_struct_0(sK0)
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),X2)) ) ),
    inference(resolution,[],[f45,f55])).

fof(f55,plain,(
    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f37,f35])).

fof(f37,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow19)).

fof(f105,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | r2_hidden(sK2,sK1) ),
    inference(resolution,[],[f104,f90])).

fof(f90,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | r2_hidden(sK2,sK1) ),
    inference(subsumption_resolution,[],[f89,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f89,plain,
    ( r2_hidden(sK2,k4_xboole_0(sK1,k1_tarski(o_0_0_xboole_0)))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | r2_hidden(sK2,sK1) ),
    inference(backward_demodulation,[],[f63,f88])).

fof(f88,plain,(
    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(o_0_0_xboole_0)) ),
    inference(forward_demodulation,[],[f87,f58])).

fof(f58,plain,(
    ! [X1] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,X1) = k4_xboole_0(sK1,X1) ),
    inference(resolution,[],[f44,f33])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f87,plain,(
    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,k1_tarski(o_0_0_xboole_0)) ),
    inference(subsumption_resolution,[],[f86,f32])).

% (14968)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f86,plain,
    ( ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,k1_tarski(o_0_0_xboole_0)) ),
    inference(subsumption_resolution,[],[f85,f31])).

fof(f85,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,k1_tarski(o_0_0_xboole_0)) ),
    inference(subsumption_resolution,[],[f84,f30])).

fof(f84,plain,
    ( v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,k1_tarski(o_0_0_xboole_0)) ),
    inference(subsumption_resolution,[],[f83,f35])).

fof(f83,plain,
    ( ~ l1_struct_0(sK0)
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,k1_tarski(o_0_0_xboole_0)) ),
    inference(subsumption_resolution,[],[f82,f34])).

fof(f82,plain,
    ( v2_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,k1_tarski(o_0_0_xboole_0)) ),
    inference(resolution,[],[f52,f33])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(o_0_0_xboole_0)) ) ),
    inference(backward_demodulation,[],[f40,f51])).

fof(f51,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[],[f38,f36])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f40,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow19)).

fof(f63,plain,
    ( v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | r2_hidden(sK2,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | r2_hidden(sK2,sK1) ),
    inference(subsumption_resolution,[],[f62,f29])).

fof(f29,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f62,plain,
    ( v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK2,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | r2_hidden(sK2,sK1) ),
    inference(subsumption_resolution,[],[f61,f34])).

fof(f61,plain,
    ( v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK2,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | r2_hidden(sK2,sK1) ),
    inference(subsumption_resolution,[],[f60,f35])).

fof(f60,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK2,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | r2_hidden(sK2,sK1) ),
    inference(resolution,[],[f43,f26])).

fof(f26,plain,
    ( r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X2,k2_yellow19(X0,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <=> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <=> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <=> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_yellow19)).

fof(f104,plain,
    ( l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | v1_xboole_0(k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f103,f32])).

fof(f103,plain,
    ( ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f102,f31])).

fof(f102,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f101,f30])).

fof(f101,plain,
    ( v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) ),
    inference(resolution,[],[f81,f33])).

fof(f81,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))
      | v1_xboole_0(k2_struct_0(sK0))
      | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),X2),sK0) ) ),
    inference(subsumption_resolution,[],[f80,f34])).

fof(f80,plain,(
    ! [X2] :
      ( v1_xboole_0(k2_struct_0(sK0))
      | v2_struct_0(sK0)
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),X2),sK0) ) ),
    inference(subsumption_resolution,[],[f75,f35])).

fof(f75,plain,(
    ! [X2] :
      ( ~ l1_struct_0(sK0)
      | v1_xboole_0(k2_struct_0(sK0))
      | v2_struct_0(sK0)
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),X2),sK0) ) ),
    inference(resolution,[],[f46,f55])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | l1_waybel_0(k3_yellow19(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f115,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | o_0_0_xboole_0 = sK2
    | ~ r2_hidden(sK2,sK1) ),
    inference(resolution,[],[f114,f27])).

fof(f27,plain,
    ( ~ r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | ~ r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f114,plain,
    ( r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | v1_xboole_0(k2_struct_0(sK0))
    | o_0_0_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f113,f104])).

fof(f113,plain,
    ( o_0_0_xboole_0 = sK2
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(subsumption_resolution,[],[f108,f100])).

fof(f108,plain,
    ( o_0_0_xboole_0 = sK2
    | v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(resolution,[],[f107,f96])).

fof(f96,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k4_xboole_0(sK1,k1_tarski(o_0_0_xboole_0)))
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
      | r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1) ) ),
    inference(subsumption_resolution,[],[f95,f34])).

fof(f95,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k4_xboole_0(sK1,k1_tarski(o_0_0_xboole_0)))
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
      | r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f92,f35])).

fof(f92,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k4_xboole_0(sK1,k1_tarski(o_0_0_xboole_0)))
      | ~ l1_struct_0(sK0)
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
      | r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f41,f88])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_yellow19(X0,X1))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | r1_waybel_0(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f107,plain,(
    ! [X0] :
      ( r2_hidden(sK2,k4_xboole_0(sK1,k1_tarski(X0)))
      | sK2 = X0
      | v1_xboole_0(k2_struct_0(sK0)) ) ),
    inference(resolution,[],[f106,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | X0 = X2
      | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f28,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f14])).

%------------------------------------------------------------------------------
