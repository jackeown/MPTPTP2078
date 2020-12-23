%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:13 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  130 (2022 expanded)
%              Number of leaves         :   15 ( 757 expanded)
%              Depth                    :   38
%              Number of atoms          :  607 (27115 expanded)
%              Number of equality atoms :   79 (1852 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f180,plain,(
    $false ),
    inference(subsumption_resolution,[],[f176,f49])).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f176,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f86,f172])).

fof(f172,plain,(
    k1_xboole_0 = k2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f171,f118])).

fof(f118,plain,
    ( m1_subset_1(sK5(sK1,sK4,sK3),k1_zfmisc_1(k2_struct_0(sK3)))
    | k1_xboole_0 = k2_struct_0(sK3) ),
    inference(forward_demodulation,[],[f117,f73])).

fof(f73,plain,(
    u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(resolution,[],[f50,f70])).

fof(f70,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f51,f41])).

fof(f41,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f30])).

% (30073)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% (30090)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f30,plain,
    ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
      | ~ v5_pre_topc(sK4,sK1,sK3)
      | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
      | ~ v1_funct_1(sK4) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v5_pre_topc(sK4,sK2,sK3)
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK4)
    & r1_tarski(u1_pre_topc(sK2),u1_pre_topc(sK1))
    & u1_struct_0(sK1) = u1_struct_0(sK2)
    & l1_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f14,f29,f28,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                      | ~ v5_pre_topc(X3,X0,X2)
                      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                      | ~ v1_funct_1(X3) )
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                    & v5_pre_topc(X3,X1,X2)
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                    & v1_funct_1(X3) )
                & r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
                & u1_struct_0(X0) = u1_struct_0(X1)
                & l1_pre_topc(X2)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2))))
                    | ~ v5_pre_topc(X3,sK1,X2)
                    | ~ v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X2))
                    | ~ v1_funct_1(X3) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                  & v5_pre_topc(X3,X1,X2)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & v1_funct_1(X3) )
              & r1_tarski(u1_pre_topc(X1),u1_pre_topc(sK1))
              & u1_struct_0(X1) = u1_struct_0(sK1)
              & l1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2))))
                  | ~ v5_pre_topc(X3,sK1,X2)
                  | ~ v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X2))
                  | ~ v1_funct_1(X3) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                & v5_pre_topc(X3,X1,X2)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & v1_funct_1(X3) )
            & r1_tarski(u1_pre_topc(X1),u1_pre_topc(sK1))
            & u1_struct_0(X1) = u1_struct_0(sK1)
            & l1_pre_topc(X2)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2))))
                | ~ v5_pre_topc(X3,sK1,X2)
                | ~ v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X2))
                | ~ v1_funct_1(X3) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X2))))
              & v5_pre_topc(X3,sK2,X2)
              & v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(X2))
              & v1_funct_1(X3) )
          & r1_tarski(u1_pre_topc(sK2),u1_pre_topc(sK1))
          & u1_struct_0(sK1) = u1_struct_0(sK2)
          & l1_pre_topc(X2)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2))))
              | ~ v5_pre_topc(X3,sK1,X2)
              | ~ v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X2))
              | ~ v1_funct_1(X3) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X2))))
            & v5_pre_topc(X3,sK2,X2)
            & v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(X2))
            & v1_funct_1(X3) )
        & r1_tarski(u1_pre_topc(sK2),u1_pre_topc(sK1))
        & u1_struct_0(sK1) = u1_struct_0(sK2)
        & l1_pre_topc(X2)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
            | ~ v5_pre_topc(X3,sK1,sK3)
            | ~ v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK3))
            | ~ v1_funct_1(X3) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
          & v5_pre_topc(X3,sK2,sK3)
          & v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(sK3))
          & v1_funct_1(X3) )
      & r1_tarski(u1_pre_topc(sK2),u1_pre_topc(sK1))
      & u1_struct_0(sK1) = u1_struct_0(sK2)
      & l1_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
          | ~ v5_pre_topc(X3,sK1,sK3)
          | ~ v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK3))
          | ~ v1_funct_1(X3) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
        & v5_pre_topc(X3,sK2,sK3)
        & v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(sK3))
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
        | ~ v5_pre_topc(sK4,sK1,sK3)
        | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
        | ~ v1_funct_1(sK4) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      & v5_pre_topc(sK4,sK2,sK3)
      & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                    | ~ v5_pre_topc(X3,X0,X2)
                    | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                    | ~ v1_funct_1(X3) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                  & v5_pre_topc(X3,X1,X2)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & v1_funct_1(X3) )
              & r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
              & u1_struct_0(X0) = u1_struct_0(X1)
              & l1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                    | ~ v5_pre_topc(X3,X0,X2)
                    | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                    | ~ v1_funct_1(X3) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                  & v5_pre_topc(X3,X1,X2)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & v1_funct_1(X3) )
              & r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
              & u1_struct_0(X0) = u1_struct_0(X1)
              & l1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( l1_pre_topc(X2)
                  & ~ v2_struct_0(X2) )
               => ( ( r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
                    & u1_struct_0(X0) = u1_struct_0(X1) )
                 => ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                        & v5_pre_topc(X3,X1,X2)
                        & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                        & v1_funct_1(X3) )
                     => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                        & v5_pre_topc(X3,X0,X2)
                        & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                        & v1_funct_1(X3) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( l1_pre_topc(X2)
                  & v2_pre_topc(X2)
                  & ~ v2_struct_0(X2) )
               => ( ( r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
                    & u1_struct_0(X0) = u1_struct_0(X1) )
                 => ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                        & v5_pre_topc(X3,X1,X2)
                        & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                        & v1_funct_1(X3) )
                     => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                        & v5_pre_topc(X3,X0,X2)
                        & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                        & v1_funct_1(X3) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ( ( r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
                  & u1_struct_0(X0) = u1_struct_0(X1) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                      & v5_pre_topc(X3,X1,X2)
                      & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                      & v1_funct_1(X3) )
                   => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                      & v5_pre_topc(X3,X0,X2)
                      & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                      & v1_funct_1(X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_tmap_1)).

fof(f51,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f50,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f117,plain,
    ( k1_xboole_0 = k2_struct_0(sK3)
    | m1_subset_1(sK5(sK1,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f111,f67])).

fof(f67,plain,(
    ~ v5_pre_topc(sK4,sK1,sK3) ),
    inference(subsumption_resolution,[],[f66,f65])).

fof(f65,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) ),
    inference(backward_demodulation,[],[f47,f42])).

fof(f42,plain,(
    u1_struct_0(sK1) = u1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f47,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f30])).

fof(f66,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
    | ~ v5_pre_topc(sK4,sK1,sK3) ),
    inference(subsumption_resolution,[],[f63,f64])).

fof(f64,plain,(
    v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3)) ),
    inference(backward_demodulation,[],[f45,f42])).

fof(f45,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f30])).

fof(f63,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
    | ~ v5_pre_topc(sK4,sK1,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f48,f44])).

fof(f44,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f48,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
    | ~ v5_pre_topc(sK4,sK1,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f111,plain,
    ( k1_xboole_0 = k2_struct_0(sK3)
    | m1_subset_1(sK5(sK1,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | v5_pre_topc(sK4,sK1,sK3) ),
    inference(resolution,[],[f107,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
      | v5_pre_topc(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( v5_pre_topc(X1,X0,X2)
          | ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,sK5(X0,X1,X2)),X0)
            & v3_pre_topc(sK5(X0,X1,X2),X2)
            & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ) )
        & ( ! [X4] :
              ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X4),X0)
              | ~ v3_pre_topc(X4,X2)
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
          | ~ v5_pre_topc(X1,X0,X2) ) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f32,f33])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X3),X0)
          & v3_pre_topc(X3,X2)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,sK5(X0,X1,X2)),X0)
        & v3_pre_topc(sK5(X0,X1,X2),X2)
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( v5_pre_topc(X1,X0,X2)
          | ? [X3] :
              ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X3),X0)
              & v3_pre_topc(X3,X2)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) )
        & ( ! [X4] :
              ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X4),X0)
              | ~ v3_pre_topc(X4,X2)
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
          | ~ v5_pre_topc(X1,X0,X2) ) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X2,X1] :
      ( ( ( v5_pre_topc(X2,X0,X1)
          | ? [X3] :
              ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
              & v3_pre_topc(X3,X1)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
        & ( ! [X3] :
              ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
              | ~ v3_pre_topc(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ v5_pre_topc(X2,X0,X1) ) )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X2,X1] :
      ( ( v5_pre_topc(X2,X0,X1)
      <=> ! [X3] :
            ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
            | ~ v3_pre_topc(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f107,plain,
    ( sP0(sK1,sK4,sK3)
    | k1_xboole_0 = k2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f106,f41])).

fof(f106,plain,
    ( sP0(sK1,sK4,sK3)
    | ~ l1_pre_topc(sK3)
    | k1_xboole_0 = k2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f105,f79])).

fof(f79,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK3)))) ),
    inference(backward_demodulation,[],[f74,f73])).

fof(f74,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK3)))) ),
    inference(backward_demodulation,[],[f65,f71])).

fof(f71,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f50,f68])).

fof(f68,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f51,f37])).

fof(f37,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f105,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK3))))
    | sP0(sK1,sK4,sK3)
    | ~ l1_pre_topc(sK3)
    | k1_xboole_0 = k2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f101,f78])).

fof(f78,plain,(
    v1_funct_2(sK4,k2_struct_0(sK1),k2_struct_0(sK3)) ),
    inference(backward_demodulation,[],[f75,f73])).

fof(f75,plain,(
    v1_funct_2(sK4,k2_struct_0(sK1),u1_struct_0(sK3)) ),
    inference(backward_demodulation,[],[f64,f71])).

fof(f101,plain,
    ( ~ v1_funct_2(sK4,k2_struct_0(sK1),k2_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK3))))
    | sP0(sK1,sK4,sK3)
    | ~ l1_pre_topc(sK3)
    | k1_xboole_0 = k2_struct_0(sK3) ),
    inference(superposition,[],[f94,f73])).

fof(f94,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK4,k2_struct_0(sK1),u1_struct_0(X0))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0))))
      | sP0(sK1,sK4,X0)
      | ~ l1_pre_topc(X0)
      | k1_xboole_0 = k2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f93,f71])).

fof(f93,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(X0))
      | sP0(sK1,sK4,X0)
      | ~ l1_pre_topc(X0)
      | k1_xboole_0 = k2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f90,f71])).

fof(f90,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(X0))
      | sP0(sK1,sK4,X0)
      | ~ l1_pre_topc(X0)
      | k1_xboole_0 = k2_struct_0(X0) ) ),
    inference(resolution,[],[f89,f37])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0))
      | sP0(X1,sK4,X0)
      | ~ l1_pre_topc(X0)
      | k1_xboole_0 = k2_struct_0(X0) ) ),
    inference(resolution,[],[f56,f44])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k1_xboole_0 = k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | sP0(X0,X2,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP0(X0,X2,X1)
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f18,f24])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k1_xboole_0 = k2_struct_0(X1)
                 => k1_xboole_0 = k2_struct_0(X0) )
               => ( v5_pre_topc(X2,X0,X1)
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( v3_pre_topc(X3,X1)
                       => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_2)).

fof(f171,plain,
    ( k1_xboole_0 = k2_struct_0(sK3)
    | ~ m1_subset_1(sK5(sK1,sK4,sK3),k1_zfmisc_1(k2_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f170,f123])).

fof(f123,plain,
    ( v3_pre_topc(sK5(sK1,sK4,sK3),sK3)
    | k1_xboole_0 = k2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f122,f118])).

fof(f122,plain,
    ( ~ m1_subset_1(sK5(sK1,sK4,sK3),k1_zfmisc_1(k2_struct_0(sK3)))
    | k1_xboole_0 = k2_struct_0(sK3)
    | v3_pre_topc(sK5(sK1,sK4,sK3),sK3) ),
    inference(forward_demodulation,[],[f121,f73])).

fof(f121,plain,
    ( k1_xboole_0 = k2_struct_0(sK3)
    | v3_pre_topc(sK5(sK1,sK4,sK3),sK3)
    | ~ m1_subset_1(sK5(sK1,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f119,f41])).

fof(f119,plain,
    ( k1_xboole_0 = k2_struct_0(sK3)
    | v3_pre_topc(sK5(sK1,sK4,sK3),sK3)
    | ~ m1_subset_1(sK5(sK1,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f116,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f116,plain,
    ( r2_hidden(sK5(sK1,sK4,sK3),u1_pre_topc(sK3))
    | k1_xboole_0 = k2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f115,f67])).

fof(f115,plain,
    ( k1_xboole_0 = k2_struct_0(sK3)
    | v5_pre_topc(sK4,sK1,sK3)
    | r2_hidden(sK5(sK1,sK4,sK3),u1_pre_topc(sK3)) ),
    inference(subsumption_resolution,[],[f110,f41])).

fof(f110,plain,
    ( k1_xboole_0 = k2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | v5_pre_topc(sK4,sK1,sK3)
    | r2_hidden(sK5(sK1,sK4,sK3),u1_pre_topc(sK3)) ),
    inference(resolution,[],[f107,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ l1_pre_topc(X2)
      | v5_pre_topc(X1,X0,X2)
      | r2_hidden(sK5(X0,X1,X2),u1_pre_topc(X2)) ) ),
    inference(subsumption_resolution,[],[f87,f53])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),u1_pre_topc(X2))
      | ~ m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | v5_pre_topc(X1,X0,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(resolution,[],[f58,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK5(X0,X1,X2),X2)
      | v5_pre_topc(X1,X0,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X1,X0)
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f170,plain,
    ( ~ v3_pre_topc(sK5(sK1,sK4,sK3),sK3)
    | k1_xboole_0 = k2_struct_0(sK3)
    | ~ m1_subset_1(sK5(sK1,sK4,sK3),k1_zfmisc_1(k2_struct_0(sK3))) ),
    inference(duplicate_literal_removal,[],[f168])).

fof(f168,plain,
    ( ~ v3_pre_topc(sK5(sK1,sK4,sK3),sK3)
    | k1_xboole_0 = k2_struct_0(sK3)
    | ~ m1_subset_1(sK5(sK1,sK4,sK3),k1_zfmisc_1(k2_struct_0(sK3)))
    | k1_xboole_0 = k2_struct_0(sK3) ),
    inference(resolution,[],[f167,f114])).

fof(f114,plain,
    ( ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,sK5(sK1,sK4,sK3)),sK1)
    | k1_xboole_0 = k2_struct_0(sK3) ),
    inference(forward_demodulation,[],[f113,f71])).

fof(f113,plain,
    ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK1),k2_struct_0(sK3),sK4,sK5(sK1,sK4,sK3)),sK1)
    | k1_xboole_0 = k2_struct_0(sK3) ),
    inference(forward_demodulation,[],[f112,f73])).

fof(f112,plain,
    ( k1_xboole_0 = k2_struct_0(sK3)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK3),sK4,sK5(sK1,sK4,sK3)),sK1) ),
    inference(subsumption_resolution,[],[f109,f67])).

fof(f109,plain,
    ( k1_xboole_0 = k2_struct_0(sK3)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK3),sK4,sK5(sK1,sK4,sK3)),sK1)
    | v5_pre_topc(sK4,sK1,sK3) ),
    inference(resolution,[],[f107,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,sK5(X0,X1,X2)),X0)
      | v5_pre_topc(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f167,plain,(
    ! [X0] :
      ( v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0),sK1)
      | ~ v3_pre_topc(X0,sK3)
      | k1_xboole_0 = k2_struct_0(sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) ) ),
    inference(subsumption_resolution,[],[f166,f79])).

fof(f166,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3)))
      | ~ v3_pre_topc(X0,sK3)
      | k1_xboole_0 = k2_struct_0(sK3)
      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0),sK1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK3)))) ) ),
    inference(resolution,[],[f165,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(f165,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0),k1_zfmisc_1(k2_struct_0(sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3)))
      | ~ v3_pre_topc(X0,sK3)
      | k1_xboole_0 = k2_struct_0(sK3)
      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0),sK1) ) ),
    inference(forward_demodulation,[],[f164,f71])).

fof(f164,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3)))
      | ~ v3_pre_topc(X0,sK3)
      | k1_xboole_0 = k2_struct_0(sK3)
      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0),sK1)
      | ~ m1_subset_1(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0),k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(subsumption_resolution,[],[f162,f37])).

fof(f162,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3)))
      | ~ v3_pre_topc(X0,sK3)
      | k1_xboole_0 = k2_struct_0(sK3)
      | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0),sK1)
      | ~ m1_subset_1(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_pre_topc(sK1) ) ),
    inference(resolution,[],[f161,f59])).

fof(f161,plain,(
    ! [X0] :
      ( r2_hidden(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0),u1_pre_topc(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3)))
      | ~ v3_pre_topc(X0,sK3)
      | k1_xboole_0 = k2_struct_0(sK3) ) ),
    inference(resolution,[],[f160,f43])).

fof(f43,plain,(
    r1_tarski(u1_pre_topc(sK2),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f160,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(u1_pre_topc(sK2),X2)
      | ~ v3_pre_topc(X1,sK3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3)))
      | r2_hidden(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X1),X2)
      | k1_xboole_0 = k2_struct_0(sK3) ) ),
    inference(resolution,[],[f158,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f158,plain,(
    ! [X0] :
      ( r2_hidden(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0),u1_pre_topc(sK2))
      | k1_xboole_0 = k2_struct_0(sK3)
      | ~ v3_pre_topc(X0,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) ) ),
    inference(subsumption_resolution,[],[f157,f79])).

fof(f157,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3)))
      | k1_xboole_0 = k2_struct_0(sK3)
      | ~ v3_pre_topc(X0,sK3)
      | r2_hidden(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0),u1_pre_topc(sK2))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK3)))) ) ),
    inference(resolution,[],[f149,f62])).

fof(f149,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0),k1_zfmisc_1(k2_struct_0(sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3)))
      | k1_xboole_0 = k2_struct_0(sK3)
      | ~ v3_pre_topc(X0,sK3)
      | r2_hidden(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0),u1_pre_topc(sK2)) ) ),
    inference(forward_demodulation,[],[f148,f76])).

fof(f76,plain,(
    u1_struct_0(sK2) = k2_struct_0(sK1) ),
    inference(backward_demodulation,[],[f42,f71])).

fof(f148,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3)))
      | k1_xboole_0 = k2_struct_0(sK3)
      | ~ v3_pre_topc(X0,sK3)
      | r2_hidden(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0),u1_pre_topc(sK2))
      | ~ m1_subset_1(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0),k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(subsumption_resolution,[],[f147,f39])).

fof(f39,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f147,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3)))
      | k1_xboole_0 = k2_struct_0(sK3)
      | ~ v3_pre_topc(X0,sK3)
      | r2_hidden(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0),u1_pre_topc(sK2))
      | ~ m1_subset_1(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_pre_topc(sK2) ) ),
    inference(resolution,[],[f146,f58])).

fof(f146,plain,(
    ! [X0] :
      ( v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0),sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3)))
      | k1_xboole_0 = k2_struct_0(sK3)
      | ~ v3_pre_topc(X0,sK3) ) ),
    inference(forward_demodulation,[],[f145,f76])).

fof(f145,plain,(
    ! [X0] :
      ( v3_pre_topc(k8_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4,X0),sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3)))
      | k1_xboole_0 = k2_struct_0(sK3)
      | ~ v3_pre_topc(X0,sK3) ) ),
    inference(forward_demodulation,[],[f144,f73])).

fof(f144,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3)))
      | k1_xboole_0 = k2_struct_0(sK3)
      | ~ v3_pre_topc(X0,sK3)
      | v3_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0),sK2) ) ),
    inference(forward_demodulation,[],[f143,f73])).

fof(f143,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_struct_0(sK3)
      | ~ v3_pre_topc(X0,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | v3_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0),sK2) ) ),
    inference(subsumption_resolution,[],[f139,f46])).

fof(f46,plain,(
    v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f139,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_struct_0(sK3)
      | ~ v3_pre_topc(X0,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ v5_pre_topc(sK4,sK2,sK3)
      | v3_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0),sK2) ) ),
    inference(resolution,[],[f138,f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ v3_pre_topc(X4,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v5_pre_topc(X1,X0,X2)
      | v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X4),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f138,plain,
    ( sP0(sK2,sK4,sK3)
    | k1_xboole_0 = k2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f137,f41])).

fof(f137,plain,
    ( sP0(sK2,sK4,sK3)
    | ~ l1_pre_topc(sK3)
    | k1_xboole_0 = k2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f136,f79])).

fof(f136,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK3))))
    | sP0(sK2,sK4,sK3)
    | ~ l1_pre_topc(sK3)
    | k1_xboole_0 = k2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f132,f78])).

fof(f132,plain,
    ( ~ v1_funct_2(sK4,k2_struct_0(sK1),k2_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK3))))
    | sP0(sK2,sK4,sK3)
    | ~ l1_pre_topc(sK3)
    | k1_xboole_0 = k2_struct_0(sK3) ),
    inference(superposition,[],[f96,f73])).

fof(f96,plain,(
    ! [X1] :
      ( ~ v1_funct_2(sK4,k2_struct_0(sK1),u1_struct_0(X1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X1))))
      | sP0(sK2,sK4,X1)
      | ~ l1_pre_topc(X1)
      | k1_xboole_0 = k2_struct_0(X1) ) ),
    inference(forward_demodulation,[],[f95,f76])).

fof(f95,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X1))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(X1))
      | sP0(sK2,sK4,X1)
      | ~ l1_pre_topc(X1)
      | k1_xboole_0 = k2_struct_0(X1) ) ),
    inference(forward_demodulation,[],[f91,f76])).

fof(f91,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(X1))
      | sP0(sK2,sK4,X1)
      | ~ l1_pre_topc(X1)
      | k1_xboole_0 = k2_struct_0(X1) ) ),
    inference(resolution,[],[f89,f39])).

fof(f86,plain,(
    ~ v1_xboole_0(k2_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f85,f40])).

% (30062)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% (30086)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% (30066)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% (30083)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f40,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f85,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK3))
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f82,f70])).

fof(f82,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK3))
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3) ),
    inference(superposition,[],[f60,f73])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.11/0.32  % Computer   : n012.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 10:21:37 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.19/0.46  % (30076)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.47  % (30085)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.47  % (30077)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.48  % (30064)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.48  % (30074)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.48  % (30069)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.49  % (30065)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.49  % (30072)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.49  % (30082)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.19/0.49  % (30068)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.49  % (30075)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.50  % (30091)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.50  % (30069)Refutation found. Thanks to Tanya!
% 0.19/0.50  % SZS status Theorem for theBenchmark
% 0.19/0.50  % SZS output start Proof for theBenchmark
% 0.19/0.50  fof(f180,plain,(
% 0.19/0.50    $false),
% 0.19/0.50    inference(subsumption_resolution,[],[f176,f49])).
% 0.19/0.50  fof(f49,plain,(
% 0.19/0.50    v1_xboole_0(k1_xboole_0)),
% 0.19/0.50    inference(cnf_transformation,[],[f2])).
% 0.19/0.50  fof(f2,axiom,(
% 0.19/0.50    v1_xboole_0(k1_xboole_0)),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.19/0.50  fof(f176,plain,(
% 0.19/0.50    ~v1_xboole_0(k1_xboole_0)),
% 0.19/0.50    inference(backward_demodulation,[],[f86,f172])).
% 0.19/0.50  fof(f172,plain,(
% 0.19/0.50    k1_xboole_0 = k2_struct_0(sK3)),
% 0.19/0.50    inference(subsumption_resolution,[],[f171,f118])).
% 0.19/0.50  fof(f118,plain,(
% 0.19/0.50    m1_subset_1(sK5(sK1,sK4,sK3),k1_zfmisc_1(k2_struct_0(sK3))) | k1_xboole_0 = k2_struct_0(sK3)),
% 0.19/0.50    inference(forward_demodulation,[],[f117,f73])).
% 0.19/0.50  fof(f73,plain,(
% 0.19/0.50    u1_struct_0(sK3) = k2_struct_0(sK3)),
% 0.19/0.50    inference(resolution,[],[f50,f70])).
% 0.19/0.50  fof(f70,plain,(
% 0.19/0.50    l1_struct_0(sK3)),
% 0.19/0.50    inference(resolution,[],[f51,f41])).
% 0.19/0.50  fof(f41,plain,(
% 0.19/0.50    l1_pre_topc(sK3)),
% 0.19/0.50    inference(cnf_transformation,[],[f30])).
% 0.19/0.50  % (30073)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.50  % (30090)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.19/0.50  fof(f30,plain,(
% 0.19/0.50    ((((~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK1,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3)) | ~v1_funct_1(sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(sK4,sK2,sK3) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4)) & r1_tarski(u1_pre_topc(sK2),u1_pre_topc(sK1)) & u1_struct_0(sK1) = u1_struct_0(sK2) & l1_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 0.19/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f14,f29,f28,f27,f26])).
% 0.19/0.50  fof(f26,plain,(
% 0.19/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) | ~v5_pre_topc(X3,X0,X2) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v5_pre_topc(X3,X1,X2) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X3)) & r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0)) & u1_struct_0(X0) = u1_struct_0(X1) & l1_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2)))) | ~v5_pre_topc(X3,sK1,X2) | ~v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X2)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v5_pre_topc(X3,X1,X2) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X3)) & r1_tarski(u1_pre_topc(X1),u1_pre_topc(sK1)) & u1_struct_0(X1) = u1_struct_0(sK1) & l1_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f27,plain,(
% 0.19/0.50    ? [X1] : (? [X2] : (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2)))) | ~v5_pre_topc(X3,sK1,X2) | ~v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X2)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v5_pre_topc(X3,X1,X2) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X3)) & r1_tarski(u1_pre_topc(X1),u1_pre_topc(sK1)) & u1_struct_0(X1) = u1_struct_0(sK1) & l1_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2)))) | ~v5_pre_topc(X3,sK1,X2) | ~v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X2)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X2)))) & v5_pre_topc(X3,sK2,X2) & v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(X2)) & v1_funct_1(X3)) & r1_tarski(u1_pre_topc(sK2),u1_pre_topc(sK1)) & u1_struct_0(sK1) = u1_struct_0(sK2) & l1_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f28,plain,(
% 0.19/0.50    ? [X2] : (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2)))) | ~v5_pre_topc(X3,sK1,X2) | ~v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X2)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X2)))) & v5_pre_topc(X3,sK2,X2) & v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(X2)) & v1_funct_1(X3)) & r1_tarski(u1_pre_topc(sK2),u1_pre_topc(sK1)) & u1_struct_0(sK1) = u1_struct_0(sK2) & l1_pre_topc(X2) & ~v2_struct_0(X2)) => (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) | ~v5_pre_topc(X3,sK1,sK3) | ~v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK3)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(X3,sK2,sK3) & v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X3)) & r1_tarski(u1_pre_topc(sK2),u1_pre_topc(sK1)) & u1_struct_0(sK1) = u1_struct_0(sK2) & l1_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f29,plain,(
% 0.19/0.50    ? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) | ~v5_pre_topc(X3,sK1,sK3) | ~v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK3)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(X3,sK2,sK3) & v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X3)) => ((~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK1,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3)) | ~v1_funct_1(sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(sK4,sK2,sK3) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f14,plain,(
% 0.19/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) | ~v5_pre_topc(X3,X0,X2) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) | ~v1_funct_1(X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v5_pre_topc(X3,X1,X2) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X3)) & r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0)) & u1_struct_0(X0) = u1_struct_0(X1) & l1_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.19/0.50    inference(flattening,[],[f13])).
% 0.19/0.50  fof(f13,plain,(
% 0.19/0.50    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) | ~v5_pre_topc(X3,X0,X2) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) | ~v1_funct_1(X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v5_pre_topc(X3,X1,X2) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X3))) & (r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0)) & u1_struct_0(X0) = u1_struct_0(X1))) & (l1_pre_topc(X2) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.19/0.50    inference(ennf_transformation,[],[f12])).
% 0.19/0.50  fof(f12,plain,(
% 0.19/0.50    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & ~v2_struct_0(X2)) => ((r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0)) & u1_struct_0(X0) = u1_struct_0(X1)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v5_pre_topc(X3,X1,X2) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X3)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) & v5_pre_topc(X3,X0,X2) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) & v1_funct_1(X3)))))))),
% 0.19/0.50    inference(pure_predicate_removal,[],[f10])).
% 0.19/0.50  fof(f10,negated_conjecture,(
% 0.19/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ((r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0)) & u1_struct_0(X0) = u1_struct_0(X1)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v5_pre_topc(X3,X1,X2) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X3)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) & v5_pre_topc(X3,X0,X2) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) & v1_funct_1(X3)))))))),
% 0.19/0.50    inference(negated_conjecture,[],[f9])).
% 0.19/0.50  fof(f9,conjecture,(
% 0.19/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ((r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0)) & u1_struct_0(X0) = u1_struct_0(X1)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v5_pre_topc(X3,X1,X2) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X3)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) & v5_pre_topc(X3,X0,X2) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) & v1_funct_1(X3)))))))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_tmap_1)).
% 0.19/0.50  fof(f51,plain,(
% 0.19/0.50    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f16])).
% 0.19/0.50  fof(f16,plain,(
% 0.19/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f6])).
% 0.19/0.50  fof(f6,axiom,(
% 0.19/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.19/0.50  fof(f50,plain,(
% 0.19/0.50    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f15])).
% 0.19/0.50  fof(f15,plain,(
% 0.19/0.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f4])).
% 0.19/0.50  fof(f4,axiom,(
% 0.19/0.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.19/0.50  fof(f117,plain,(
% 0.19/0.50    k1_xboole_0 = k2_struct_0(sK3) | m1_subset_1(sK5(sK1,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.19/0.50    inference(subsumption_resolution,[],[f111,f67])).
% 0.19/0.50  fof(f67,plain,(
% 0.19/0.50    ~v5_pre_topc(sK4,sK1,sK3)),
% 0.19/0.50    inference(subsumption_resolution,[],[f66,f65])).
% 0.19/0.50  fof(f65,plain,(
% 0.19/0.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))),
% 0.19/0.50    inference(backward_demodulation,[],[f47,f42])).
% 0.19/0.50  fof(f42,plain,(
% 0.19/0.50    u1_struct_0(sK1) = u1_struct_0(sK2)),
% 0.19/0.50    inference(cnf_transformation,[],[f30])).
% 0.19/0.50  fof(f47,plain,(
% 0.19/0.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 0.19/0.50    inference(cnf_transformation,[],[f30])).
% 0.19/0.50  fof(f66,plain,(
% 0.19/0.50    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK1,sK3)),
% 0.19/0.50    inference(subsumption_resolution,[],[f63,f64])).
% 0.19/0.50  fof(f64,plain,(
% 0.19/0.50    v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))),
% 0.19/0.50    inference(backward_demodulation,[],[f45,f42])).
% 0.19/0.50  fof(f45,plain,(
% 0.19/0.50    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 0.19/0.50    inference(cnf_transformation,[],[f30])).
% 0.19/0.50  fof(f63,plain,(
% 0.19/0.50    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK1,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3))),
% 0.19/0.50    inference(subsumption_resolution,[],[f48,f44])).
% 0.19/0.50  fof(f44,plain,(
% 0.19/0.50    v1_funct_1(sK4)),
% 0.19/0.50    inference(cnf_transformation,[],[f30])).
% 0.19/0.50  fof(f48,plain,(
% 0.19/0.50    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK1,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 0.19/0.50    inference(cnf_transformation,[],[f30])).
% 0.19/0.50  fof(f111,plain,(
% 0.19/0.50    k1_xboole_0 = k2_struct_0(sK3) | m1_subset_1(sK5(sK1,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK3))) | v5_pre_topc(sK4,sK1,sK3)),
% 0.19/0.50    inference(resolution,[],[f107,f53])).
% 0.19/0.50  fof(f53,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) | v5_pre_topc(X1,X0,X2)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f34])).
% 0.19/0.50  fof(f34,plain,(
% 0.19/0.50    ! [X0,X1,X2] : (((v5_pre_topc(X1,X0,X2) | (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,sK5(X0,X1,X2)),X0) & v3_pre_topc(sK5(X0,X1,X2),X2) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))))) & (! [X4] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X4),X0) | ~v3_pre_topc(X4,X2) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))) | ~v5_pre_topc(X1,X0,X2))) | ~sP0(X0,X1,X2))),
% 0.19/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f32,f33])).
% 0.19/0.50  fof(f33,plain,(
% 0.19/0.50    ! [X2,X1,X0] : (? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X3),X0) & v3_pre_topc(X3,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) => (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,sK5(X0,X1,X2)),X0) & v3_pre_topc(sK5(X0,X1,X2),X2) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f32,plain,(
% 0.19/0.50    ! [X0,X1,X2] : (((v5_pre_topc(X1,X0,X2) | ? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X3),X0) & v3_pre_topc(X3,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))) & (! [X4] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X4),X0) | ~v3_pre_topc(X4,X2) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))) | ~v5_pre_topc(X1,X0,X2))) | ~sP0(X0,X1,X2))),
% 0.19/0.50    inference(rectify,[],[f31])).
% 0.19/0.50  fof(f31,plain,(
% 0.19/0.50    ! [X0,X2,X1] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~sP0(X0,X2,X1))),
% 0.19/0.50    inference(nnf_transformation,[],[f24])).
% 0.19/0.50  fof(f24,plain,(
% 0.19/0.50    ! [X0,X2,X1] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~sP0(X0,X2,X1))),
% 0.19/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.19/0.50  fof(f107,plain,(
% 0.19/0.50    sP0(sK1,sK4,sK3) | k1_xboole_0 = k2_struct_0(sK3)),
% 0.19/0.50    inference(subsumption_resolution,[],[f106,f41])).
% 0.19/0.50  fof(f106,plain,(
% 0.19/0.50    sP0(sK1,sK4,sK3) | ~l1_pre_topc(sK3) | k1_xboole_0 = k2_struct_0(sK3)),
% 0.19/0.50    inference(subsumption_resolution,[],[f105,f79])).
% 0.19/0.50  fof(f79,plain,(
% 0.19/0.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK3))))),
% 0.19/0.50    inference(backward_demodulation,[],[f74,f73])).
% 0.19/0.50  fof(f74,plain,(
% 0.19/0.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK3))))),
% 0.19/0.50    inference(backward_demodulation,[],[f65,f71])).
% 0.19/0.50  fof(f71,plain,(
% 0.19/0.50    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.19/0.50    inference(resolution,[],[f50,f68])).
% 0.19/0.50  fof(f68,plain,(
% 0.19/0.50    l1_struct_0(sK1)),
% 0.19/0.50    inference(resolution,[],[f51,f37])).
% 0.19/0.50  fof(f37,plain,(
% 0.19/0.50    l1_pre_topc(sK1)),
% 0.19/0.50    inference(cnf_transformation,[],[f30])).
% 0.19/0.50  fof(f105,plain,(
% 0.19/0.50    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK3)))) | sP0(sK1,sK4,sK3) | ~l1_pre_topc(sK3) | k1_xboole_0 = k2_struct_0(sK3)),
% 0.19/0.50    inference(subsumption_resolution,[],[f101,f78])).
% 0.19/0.50  fof(f78,plain,(
% 0.19/0.50    v1_funct_2(sK4,k2_struct_0(sK1),k2_struct_0(sK3))),
% 0.19/0.50    inference(backward_demodulation,[],[f75,f73])).
% 0.19/0.50  fof(f75,plain,(
% 0.19/0.50    v1_funct_2(sK4,k2_struct_0(sK1),u1_struct_0(sK3))),
% 0.19/0.50    inference(backward_demodulation,[],[f64,f71])).
% 0.19/0.50  fof(f101,plain,(
% 0.19/0.50    ~v1_funct_2(sK4,k2_struct_0(sK1),k2_struct_0(sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK3)))) | sP0(sK1,sK4,sK3) | ~l1_pre_topc(sK3) | k1_xboole_0 = k2_struct_0(sK3)),
% 0.19/0.50    inference(superposition,[],[f94,f73])).
% 0.19/0.50  fof(f94,plain,(
% 0.19/0.50    ( ! [X0] : (~v1_funct_2(sK4,k2_struct_0(sK1),u1_struct_0(X0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0)))) | sP0(sK1,sK4,X0) | ~l1_pre_topc(X0) | k1_xboole_0 = k2_struct_0(X0)) )),
% 0.19/0.50    inference(forward_demodulation,[],[f93,f71])).
% 0.19/0.50  fof(f93,plain,(
% 0.19/0.50    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X0)))) | ~v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(X0)) | sP0(sK1,sK4,X0) | ~l1_pre_topc(X0) | k1_xboole_0 = k2_struct_0(X0)) )),
% 0.19/0.50    inference(forward_demodulation,[],[f90,f71])).
% 0.19/0.50  fof(f90,plain,(
% 0.19/0.50    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(X0)) | sP0(sK1,sK4,X0) | ~l1_pre_topc(X0) | k1_xboole_0 = k2_struct_0(X0)) )),
% 0.19/0.50    inference(resolution,[],[f89,f37])).
% 0.19/0.50  fof(f89,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0)) | sP0(X1,sK4,X0) | ~l1_pre_topc(X0) | k1_xboole_0 = k2_struct_0(X0)) )),
% 0.19/0.50    inference(resolution,[],[f56,f44])).
% 0.19/0.50  fof(f56,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k1_xboole_0 = k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | sP0(X0,X2,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f25])).
% 0.19/0.50  fof(f25,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (! [X2] : (sP0(X0,X2,X1) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.19/0.50    inference(definition_folding,[],[f18,f24])).
% 0.19/0.50  fof(f18,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.19/0.50    inference(flattening,[],[f17])).
% 0.19/0.50  fof(f17,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f8])).
% 0.19/0.50  fof(f8,axiom,(
% 0.19/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v3_pre_topc(X3,X1) => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0))))))))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_2)).
% 0.19/0.50  fof(f171,plain,(
% 0.19/0.50    k1_xboole_0 = k2_struct_0(sK3) | ~m1_subset_1(sK5(sK1,sK4,sK3),k1_zfmisc_1(k2_struct_0(sK3)))),
% 0.19/0.50    inference(subsumption_resolution,[],[f170,f123])).
% 0.19/0.50  fof(f123,plain,(
% 0.19/0.50    v3_pre_topc(sK5(sK1,sK4,sK3),sK3) | k1_xboole_0 = k2_struct_0(sK3)),
% 0.19/0.50    inference(subsumption_resolution,[],[f122,f118])).
% 0.19/0.50  fof(f122,plain,(
% 0.19/0.50    ~m1_subset_1(sK5(sK1,sK4,sK3),k1_zfmisc_1(k2_struct_0(sK3))) | k1_xboole_0 = k2_struct_0(sK3) | v3_pre_topc(sK5(sK1,sK4,sK3),sK3)),
% 0.19/0.50    inference(forward_demodulation,[],[f121,f73])).
% 0.19/0.50  fof(f121,plain,(
% 0.19/0.50    k1_xboole_0 = k2_struct_0(sK3) | v3_pre_topc(sK5(sK1,sK4,sK3),sK3) | ~m1_subset_1(sK5(sK1,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.19/0.50    inference(subsumption_resolution,[],[f119,f41])).
% 0.19/0.50  fof(f119,plain,(
% 0.19/0.50    k1_xboole_0 = k2_struct_0(sK3) | v3_pre_topc(sK5(sK1,sK4,sK3),sK3) | ~m1_subset_1(sK5(sK1,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK3)),
% 0.19/0.50    inference(resolution,[],[f116,f59])).
% 0.19/0.50  fof(f59,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~r2_hidden(X1,u1_pre_topc(X0)) | v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f35])).
% 0.19/0.50  fof(f35,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.50    inference(nnf_transformation,[],[f19])).
% 0.19/0.50  fof(f19,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f5])).
% 0.19/0.50  fof(f5,axiom,(
% 0.19/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).
% 0.19/0.50  fof(f116,plain,(
% 0.19/0.50    r2_hidden(sK5(sK1,sK4,sK3),u1_pre_topc(sK3)) | k1_xboole_0 = k2_struct_0(sK3)),
% 0.19/0.50    inference(subsumption_resolution,[],[f115,f67])).
% 0.19/0.50  fof(f115,plain,(
% 0.19/0.50    k1_xboole_0 = k2_struct_0(sK3) | v5_pre_topc(sK4,sK1,sK3) | r2_hidden(sK5(sK1,sK4,sK3),u1_pre_topc(sK3))),
% 0.19/0.50    inference(subsumption_resolution,[],[f110,f41])).
% 0.19/0.50  fof(f110,plain,(
% 0.19/0.50    k1_xboole_0 = k2_struct_0(sK3) | ~l1_pre_topc(sK3) | v5_pre_topc(sK4,sK1,sK3) | r2_hidden(sK5(sK1,sK4,sK3),u1_pre_topc(sK3))),
% 0.19/0.50    inference(resolution,[],[f107,f88])).
% 0.19/0.50  fof(f88,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~l1_pre_topc(X2) | v5_pre_topc(X1,X0,X2) | r2_hidden(sK5(X0,X1,X2),u1_pre_topc(X2))) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f87,f53])).
% 0.19/0.50  fof(f87,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),u1_pre_topc(X2)) | ~m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | v5_pre_topc(X1,X0,X2) | ~sP0(X0,X1,X2)) )),
% 0.19/0.50    inference(resolution,[],[f58,f54])).
% 0.19/0.50  fof(f54,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (v3_pre_topc(sK5(X0,X1,X2),X2) | v5_pre_topc(X1,X0,X2) | ~sP0(X0,X1,X2)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f34])).
% 0.19/0.50  fof(f58,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~v3_pre_topc(X1,X0) | r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f35])).
% 0.19/0.50  fof(f170,plain,(
% 0.19/0.50    ~v3_pre_topc(sK5(sK1,sK4,sK3),sK3) | k1_xboole_0 = k2_struct_0(sK3) | ~m1_subset_1(sK5(sK1,sK4,sK3),k1_zfmisc_1(k2_struct_0(sK3)))),
% 0.19/0.50    inference(duplicate_literal_removal,[],[f168])).
% 0.19/0.50  fof(f168,plain,(
% 0.19/0.50    ~v3_pre_topc(sK5(sK1,sK4,sK3),sK3) | k1_xboole_0 = k2_struct_0(sK3) | ~m1_subset_1(sK5(sK1,sK4,sK3),k1_zfmisc_1(k2_struct_0(sK3))) | k1_xboole_0 = k2_struct_0(sK3)),
% 0.19/0.50    inference(resolution,[],[f167,f114])).
% 0.19/0.50  fof(f114,plain,(
% 0.19/0.50    ~v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,sK5(sK1,sK4,sK3)),sK1) | k1_xboole_0 = k2_struct_0(sK3)),
% 0.19/0.50    inference(forward_demodulation,[],[f113,f71])).
% 0.19/0.50  fof(f113,plain,(
% 0.19/0.50    ~v3_pre_topc(k8_relset_1(u1_struct_0(sK1),k2_struct_0(sK3),sK4,sK5(sK1,sK4,sK3)),sK1) | k1_xboole_0 = k2_struct_0(sK3)),
% 0.19/0.50    inference(forward_demodulation,[],[f112,f73])).
% 0.19/0.50  fof(f112,plain,(
% 0.19/0.50    k1_xboole_0 = k2_struct_0(sK3) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK3),sK4,sK5(sK1,sK4,sK3)),sK1)),
% 0.19/0.50    inference(subsumption_resolution,[],[f109,f67])).
% 0.19/0.50  fof(f109,plain,(
% 0.19/0.50    k1_xboole_0 = k2_struct_0(sK3) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK3),sK4,sK5(sK1,sK4,sK3)),sK1) | v5_pre_topc(sK4,sK1,sK3)),
% 0.19/0.50    inference(resolution,[],[f107,f55])).
% 0.19/0.50  fof(f55,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,sK5(X0,X1,X2)),X0) | v5_pre_topc(X1,X0,X2)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f34])).
% 0.19/0.50  fof(f167,plain,(
% 0.19/0.50    ( ! [X0] : (v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0),sK1) | ~v3_pre_topc(X0,sK3) | k1_xboole_0 = k2_struct_0(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3)))) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f166,f79])).
% 0.19/0.50  fof(f166,plain,(
% 0.19/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) | ~v3_pre_topc(X0,sK3) | k1_xboole_0 = k2_struct_0(sK3) | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0),sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK3))))) )),
% 0.19/0.50    inference(resolution,[],[f165,f62])).
% 0.19/0.50  fof(f62,plain,(
% 0.19/0.50    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f23])).
% 0.19/0.50  fof(f23,plain,(
% 0.19/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.50    inference(ennf_transformation,[],[f3])).
% 0.19/0.50  fof(f3,axiom,(
% 0.19/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).
% 0.19/0.50  fof(f165,plain,(
% 0.19/0.50    ( ! [X0] : (~m1_subset_1(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0),k1_zfmisc_1(k2_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) | ~v3_pre_topc(X0,sK3) | k1_xboole_0 = k2_struct_0(sK3) | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0),sK1)) )),
% 0.19/0.50    inference(forward_demodulation,[],[f164,f71])).
% 0.19/0.50  fof(f164,plain,(
% 0.19/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) | ~v3_pre_topc(X0,sK3) | k1_xboole_0 = k2_struct_0(sK3) | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0),sK1) | ~m1_subset_1(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0),k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f162,f37])).
% 0.19/0.50  fof(f162,plain,(
% 0.19/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) | ~v3_pre_topc(X0,sK3) | k1_xboole_0 = k2_struct_0(sK3) | v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0),sK1) | ~m1_subset_1(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)) )),
% 0.19/0.50    inference(resolution,[],[f161,f59])).
% 0.19/0.50  fof(f161,plain,(
% 0.19/0.50    ( ! [X0] : (r2_hidden(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0),u1_pre_topc(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) | ~v3_pre_topc(X0,sK3) | k1_xboole_0 = k2_struct_0(sK3)) )),
% 0.19/0.50    inference(resolution,[],[f160,f43])).
% 0.19/0.50  fof(f43,plain,(
% 0.19/0.50    r1_tarski(u1_pre_topc(sK2),u1_pre_topc(sK1))),
% 0.19/0.50    inference(cnf_transformation,[],[f30])).
% 0.19/0.50  fof(f160,plain,(
% 0.19/0.50    ( ! [X2,X1] : (~r1_tarski(u1_pre_topc(sK2),X2) | ~v3_pre_topc(X1,sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) | r2_hidden(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X1),X2) | k1_xboole_0 = k2_struct_0(sK3)) )),
% 0.19/0.50    inference(resolution,[],[f158,f61])).
% 0.19/0.50  fof(f61,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f22])).
% 0.19/0.50  fof(f22,plain,(
% 0.19/0.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 0.19/0.50    inference(ennf_transformation,[],[f11])).
% 0.19/0.50  fof(f11,plain,(
% 0.19/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.19/0.50    inference(unused_predicate_definition_removal,[],[f1])).
% 0.19/0.50  fof(f1,axiom,(
% 0.19/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.19/0.50  fof(f158,plain,(
% 0.19/0.50    ( ! [X0] : (r2_hidden(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0),u1_pre_topc(sK2)) | k1_xboole_0 = k2_struct_0(sK3) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3)))) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f157,f79])).
% 0.19/0.50  fof(f157,plain,(
% 0.19/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) | k1_xboole_0 = k2_struct_0(sK3) | ~v3_pre_topc(X0,sK3) | r2_hidden(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0),u1_pre_topc(sK2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK3))))) )),
% 0.19/0.50    inference(resolution,[],[f149,f62])).
% 0.19/0.50  fof(f149,plain,(
% 0.19/0.50    ( ! [X0] : (~m1_subset_1(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0),k1_zfmisc_1(k2_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) | k1_xboole_0 = k2_struct_0(sK3) | ~v3_pre_topc(X0,sK3) | r2_hidden(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0),u1_pre_topc(sK2))) )),
% 0.19/0.50    inference(forward_demodulation,[],[f148,f76])).
% 0.19/0.50  fof(f76,plain,(
% 0.19/0.50    u1_struct_0(sK2) = k2_struct_0(sK1)),
% 0.19/0.50    inference(backward_demodulation,[],[f42,f71])).
% 0.19/0.50  fof(f148,plain,(
% 0.19/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) | k1_xboole_0 = k2_struct_0(sK3) | ~v3_pre_topc(X0,sK3) | r2_hidden(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0),u1_pre_topc(sK2)) | ~m1_subset_1(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0),k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f147,f39])).
% 0.19/0.50  fof(f39,plain,(
% 0.19/0.50    l1_pre_topc(sK2)),
% 0.19/0.50    inference(cnf_transformation,[],[f30])).
% 0.19/0.50  fof(f147,plain,(
% 0.19/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) | k1_xboole_0 = k2_struct_0(sK3) | ~v3_pre_topc(X0,sK3) | r2_hidden(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0),u1_pre_topc(sK2)) | ~m1_subset_1(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0),k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)) )),
% 0.19/0.50    inference(resolution,[],[f146,f58])).
% 0.19/0.50  fof(f146,plain,(
% 0.19/0.50    ( ! [X0] : (v3_pre_topc(k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK3),sK4,X0),sK2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) | k1_xboole_0 = k2_struct_0(sK3) | ~v3_pre_topc(X0,sK3)) )),
% 0.19/0.50    inference(forward_demodulation,[],[f145,f76])).
% 0.19/0.50  fof(f145,plain,(
% 0.19/0.50    ( ! [X0] : (v3_pre_topc(k8_relset_1(u1_struct_0(sK2),k2_struct_0(sK3),sK4,X0),sK2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) | k1_xboole_0 = k2_struct_0(sK3) | ~v3_pre_topc(X0,sK3)) )),
% 0.19/0.50    inference(forward_demodulation,[],[f144,f73])).
% 0.19/0.50  fof(f144,plain,(
% 0.19/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) | k1_xboole_0 = k2_struct_0(sK3) | ~v3_pre_topc(X0,sK3) | v3_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0),sK2)) )),
% 0.19/0.50    inference(forward_demodulation,[],[f143,f73])).
% 0.19/0.50  fof(f143,plain,(
% 0.19/0.50    ( ! [X0] : (k1_xboole_0 = k2_struct_0(sK3) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | v3_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0),sK2)) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f139,f46])).
% 0.19/0.50  fof(f46,plain,(
% 0.19/0.50    v5_pre_topc(sK4,sK2,sK3)),
% 0.19/0.50    inference(cnf_transformation,[],[f30])).
% 0.19/0.50  fof(f139,plain,(
% 0.19/0.50    ( ! [X0] : (k1_xboole_0 = k2_struct_0(sK3) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~v5_pre_topc(sK4,sK2,sK3) | v3_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0),sK2)) )),
% 0.19/0.50    inference(resolution,[],[f138,f52])).
% 0.19/0.50  fof(f52,plain,(
% 0.19/0.50    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~v3_pre_topc(X4,X2) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) | ~v5_pre_topc(X1,X0,X2) | v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X4),X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f34])).
% 0.19/0.50  fof(f138,plain,(
% 0.19/0.50    sP0(sK2,sK4,sK3) | k1_xboole_0 = k2_struct_0(sK3)),
% 0.19/0.50    inference(subsumption_resolution,[],[f137,f41])).
% 0.19/0.50  fof(f137,plain,(
% 0.19/0.50    sP0(sK2,sK4,sK3) | ~l1_pre_topc(sK3) | k1_xboole_0 = k2_struct_0(sK3)),
% 0.19/0.50    inference(subsumption_resolution,[],[f136,f79])).
% 0.19/0.50  fof(f136,plain,(
% 0.19/0.50    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK3)))) | sP0(sK2,sK4,sK3) | ~l1_pre_topc(sK3) | k1_xboole_0 = k2_struct_0(sK3)),
% 0.19/0.50    inference(subsumption_resolution,[],[f132,f78])).
% 0.19/0.50  fof(f132,plain,(
% 0.19/0.50    ~v1_funct_2(sK4,k2_struct_0(sK1),k2_struct_0(sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK3)))) | sP0(sK2,sK4,sK3) | ~l1_pre_topc(sK3) | k1_xboole_0 = k2_struct_0(sK3)),
% 0.19/0.50    inference(superposition,[],[f96,f73])).
% 0.19/0.50  fof(f96,plain,(
% 0.19/0.50    ( ! [X1] : (~v1_funct_2(sK4,k2_struct_0(sK1),u1_struct_0(X1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X1)))) | sP0(sK2,sK4,X1) | ~l1_pre_topc(X1) | k1_xboole_0 = k2_struct_0(X1)) )),
% 0.19/0.50    inference(forward_demodulation,[],[f95,f76])).
% 0.19/0.50  fof(f95,plain,(
% 0.19/0.50    ( ! [X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(X1)) | sP0(sK2,sK4,X1) | ~l1_pre_topc(X1) | k1_xboole_0 = k2_struct_0(X1)) )),
% 0.19/0.50    inference(forward_demodulation,[],[f91,f76])).
% 0.19/0.50  fof(f91,plain,(
% 0.19/0.50    ( ! [X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(X1)) | sP0(sK2,sK4,X1) | ~l1_pre_topc(X1) | k1_xboole_0 = k2_struct_0(X1)) )),
% 0.19/0.50    inference(resolution,[],[f89,f39])).
% 0.19/0.50  fof(f86,plain,(
% 0.19/0.50    ~v1_xboole_0(k2_struct_0(sK3))),
% 0.19/0.50    inference(subsumption_resolution,[],[f85,f40])).
% 0.19/0.51  % (30062)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.51  % (30086)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.51  % (30066)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.51  % (30083)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.51  fof(f40,plain,(
% 0.19/0.51    ~v2_struct_0(sK3)),
% 0.19/0.51    inference(cnf_transformation,[],[f30])).
% 0.19/0.51  fof(f85,plain,(
% 0.19/0.51    ~v1_xboole_0(k2_struct_0(sK3)) | v2_struct_0(sK3)),
% 0.19/0.51    inference(subsumption_resolution,[],[f82,f70])).
% 0.19/0.51  fof(f82,plain,(
% 0.19/0.51    ~v1_xboole_0(k2_struct_0(sK3)) | ~l1_struct_0(sK3) | v2_struct_0(sK3)),
% 0.19/0.51    inference(superposition,[],[f60,f73])).
% 0.19/0.51  fof(f60,plain,(
% 0.19/0.51    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f21])).
% 0.19/0.51  fof(f21,plain,(
% 0.19/0.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.19/0.51    inference(flattening,[],[f20])).
% 0.19/0.51  fof(f20,plain,(
% 0.19/0.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f7])).
% 0.19/0.51  fof(f7,axiom,(
% 0.19/0.51    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.19/0.51  % SZS output end Proof for theBenchmark
% 0.19/0.51  % (30069)------------------------------
% 0.19/0.51  % (30069)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (30069)Termination reason: Refutation
% 0.19/0.51  
% 0.19/0.51  % (30069)Memory used [KB]: 6396
% 0.19/0.51  % (30069)Time elapsed: 0.097 s
% 0.19/0.51  % (30069)------------------------------
% 0.19/0.51  % (30069)------------------------------
% 0.19/0.51  % (30079)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.19/0.51  % (30063)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.51  % (30067)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.51  % (30088)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.19/0.51  % (30061)Success in time 0.177 s
%------------------------------------------------------------------------------
