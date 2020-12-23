%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:56 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 260 expanded)
%              Number of leaves         :   13 (  60 expanded)
%              Depth                    :   17
%              Number of atoms          :  256 (1603 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f170,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f65,f90,f163,f169])).

fof(f169,plain,
    ( spl6_3
    | ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f168])).

fof(f168,plain,
    ( $false
    | spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f167,f60])).

fof(f60,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl6_3
  <=> r1_tsep_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f167,plain,
    ( r1_tsep_1(sK3,sK1)
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f166,f75])).

fof(f75,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f72,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f72,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f69,f33])).

fof(f33,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
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
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

% (14562)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( m1_pre_topc(X1,X2)
                     => ( ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) )
                        | ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( m1_pre_topc(X1,X2)
                   => ( ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) )
                      | ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tmap_1)).

fof(f69,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK1) ),
    inference(resolution,[],[f37,f30])).

fof(f30,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f166,plain,
    ( ~ l1_struct_0(sK1)
    | r1_tsep_1(sK3,sK1)
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f165,f74])).

fof(f74,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f71,f36])).

fof(f71,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f67,f33])).

fof(f67,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(resolution,[],[f37,f25])).

fof(f25,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f165,plain,
    ( ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK1)
    | r1_tsep_1(sK3,sK1)
    | ~ spl6_4 ),
    inference(resolution,[],[f63,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0)
      | r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f63,plain,
    ( r1_tsep_1(sK1,sK3)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl6_4
  <=> r1_tsep_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f163,plain,
    ( spl6_4
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f162,f49,f62])).

fof(f49,plain,
    ( spl6_1
  <=> r1_tsep_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f162,plain,
    ( r1_tsep_1(sK1,sK3)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f161,f75])).

fof(f161,plain,
    ( ~ l1_struct_0(sK1)
    | r1_tsep_1(sK1,sK3)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f159,f74])).

fof(f159,plain,
    ( ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK1)
    | r1_tsep_1(sK1,sK3)
    | ~ spl6_1 ),
    inference(resolution,[],[f158,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0)
      | r1_tsep_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f158,plain,
    ( r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ spl6_1 ),
    inference(resolution,[],[f152,f128])).

fof(f128,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f127,f74])).

fof(f127,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ l1_struct_0(sK3)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f124,f76])).

fof(f76,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f73,f36])).

fof(f73,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f70,f33])).

fof(f70,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(resolution,[],[f37,f28])).

fof(f28,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f124,plain,
    ( ~ l1_struct_0(sK2)
    | r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ l1_struct_0(sK3)
    | ~ spl6_1 ),
    inference(resolution,[],[f35,f51])).

fof(f51,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f152,plain,(
    ! [X4] :
      ( ~ r1_xboole_0(X4,u1_struct_0(sK2))
      | r1_xboole_0(u1_struct_0(sK1),X4) ) ),
    inference(duplicate_literal_removal,[],[f149])).

fof(f149,plain,(
    ! [X4] :
      ( r1_xboole_0(u1_struct_0(sK1),X4)
      | ~ r1_xboole_0(X4,u1_struct_0(sK2))
      | r1_xboole_0(u1_struct_0(sK1),X4) ) ),
    inference(resolution,[],[f120,f82])).

fof(f82,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(sK4(X3,X4),X5)
      | ~ r1_xboole_0(X4,X5)
      | r1_xboole_0(X3,X4) ) ),
    inference(resolution,[],[f39,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f120,plain,(
    ! [X3] :
      ( r2_hidden(sK4(u1_struct_0(sK1),X3),u1_struct_0(sK2))
      | r1_xboole_0(u1_struct_0(sK1),X3) ) ),
    inference(resolution,[],[f84,f102])).

fof(f102,plain,(
    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(resolution,[],[f97,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f97,plain,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f93,f73])).

fof(f93,plain,
    ( ~ l1_pre_topc(sK2)
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(resolution,[],[f38,f26])).

fof(f26,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | r2_hidden(sK4(X0,X1),X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f43,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f90,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f89,f53,f49])).

fof(f53,plain,
    ( spl6_2
  <=> r1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f89,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f88,f76])).

fof(f88,plain,
    ( ~ l1_struct_0(sK2)
    | r1_tsep_1(sK3,sK2)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f87,f74])).

fof(f87,plain,
    ( ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | r1_tsep_1(sK3,sK2)
    | ~ spl6_2 ),
    inference(resolution,[],[f42,f55])).

fof(f55,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f65,plain,
    ( ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f23,f62,f58])).

fof(f23,plain,
    ( ~ r1_tsep_1(sK1,sK3)
    | ~ r1_tsep_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f56,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f22,f53,f49])).

fof(f22,plain,
    ( r1_tsep_1(sK2,sK3)
    | r1_tsep_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:35:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (14567)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.20/0.47  % (14567)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f170,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f56,f65,f90,f163,f169])).
% 0.20/0.47  fof(f169,plain,(
% 0.20/0.47    spl6_3 | ~spl6_4),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f168])).
% 0.20/0.47  fof(f168,plain,(
% 0.20/0.47    $false | (spl6_3 | ~spl6_4)),
% 0.20/0.47    inference(subsumption_resolution,[],[f167,f60])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    ~r1_tsep_1(sK3,sK1) | spl6_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f58])).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    spl6_3 <=> r1_tsep_1(sK3,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.47  fof(f167,plain,(
% 0.20/0.47    r1_tsep_1(sK3,sK1) | ~spl6_4),
% 0.20/0.47    inference(subsumption_resolution,[],[f166,f75])).
% 0.20/0.47  fof(f75,plain,(
% 0.20/0.47    l1_struct_0(sK1)),
% 0.20/0.47    inference(resolution,[],[f72,f36])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    l1_pre_topc(sK1)),
% 0.20/0.47    inference(subsumption_resolution,[],[f69,f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    l1_pre_topc(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3))) & m1_pre_topc(X1,X2)) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f10])).
% 0.20/0.47  % (14562)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.20/0.47  fof(f10,negated_conjecture,(
% 0.20/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 0.20/0.47    inference(negated_conjecture,[],[f9])).
% 0.20/0.47  fof(f9,conjecture,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tmap_1)).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    ~l1_pre_topc(sK0) | l1_pre_topc(sK1)),
% 0.20/0.47    inference(resolution,[],[f37,f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    m1_pre_topc(sK1,sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.47  fof(f166,plain,(
% 0.20/0.47    ~l1_struct_0(sK1) | r1_tsep_1(sK3,sK1) | ~spl6_4),
% 0.20/0.47    inference(subsumption_resolution,[],[f165,f74])).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    l1_struct_0(sK3)),
% 0.20/0.47    inference(resolution,[],[f71,f36])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    l1_pre_topc(sK3)),
% 0.20/0.47    inference(subsumption_resolution,[],[f67,f33])).
% 0.20/0.47  fof(f67,plain,(
% 0.20/0.47    ~l1_pre_topc(sK0) | l1_pre_topc(sK3)),
% 0.20/0.47    inference(resolution,[],[f37,f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    m1_pre_topc(sK3,sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f165,plain,(
% 0.20/0.47    ~l1_struct_0(sK3) | ~l1_struct_0(sK1) | r1_tsep_1(sK3,sK1) | ~spl6_4),
% 0.20/0.47    inference(resolution,[],[f63,f42])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0) | r1_tsep_1(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    r1_tsep_1(sK1,sK3) | ~spl6_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f62])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    spl6_4 <=> r1_tsep_1(sK1,sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.47  fof(f163,plain,(
% 0.20/0.47    spl6_4 | ~spl6_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f162,f49,f62])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    spl6_1 <=> r1_tsep_1(sK3,sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.47  fof(f162,plain,(
% 0.20/0.47    r1_tsep_1(sK1,sK3) | ~spl6_1),
% 0.20/0.47    inference(subsumption_resolution,[],[f161,f75])).
% 0.20/0.47  fof(f161,plain,(
% 0.20/0.47    ~l1_struct_0(sK1) | r1_tsep_1(sK1,sK3) | ~spl6_1),
% 0.20/0.47    inference(subsumption_resolution,[],[f159,f74])).
% 0.20/0.47  fof(f159,plain,(
% 0.20/0.47    ~l1_struct_0(sK3) | ~l1_struct_0(sK1) | r1_tsep_1(sK1,sK3) | ~spl6_1),
% 0.20/0.47    inference(resolution,[],[f158,f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~l1_struct_0(X0) | r1_tsep_1(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).
% 0.20/0.47  fof(f158,plain,(
% 0.20/0.47    r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) | ~spl6_1),
% 0.20/0.47    inference(resolution,[],[f152,f128])).
% 0.20/0.47  fof(f128,plain,(
% 0.20/0.47    r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) | ~spl6_1),
% 0.20/0.47    inference(subsumption_resolution,[],[f127,f74])).
% 0.20/0.47  fof(f127,plain,(
% 0.20/0.47    r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) | ~l1_struct_0(sK3) | ~spl6_1),
% 0.20/0.47    inference(subsumption_resolution,[],[f124,f76])).
% 0.20/0.47  fof(f76,plain,(
% 0.20/0.47    l1_struct_0(sK2)),
% 0.20/0.47    inference(resolution,[],[f73,f36])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    l1_pre_topc(sK2)),
% 0.20/0.47    inference(subsumption_resolution,[],[f70,f33])).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    ~l1_pre_topc(sK0) | l1_pre_topc(sK2)),
% 0.20/0.47    inference(resolution,[],[f37,f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    m1_pre_topc(sK2,sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f124,plain,(
% 0.20/0.47    ~l1_struct_0(sK2) | r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) | ~l1_struct_0(sK3) | ~spl6_1),
% 0.20/0.47    inference(resolution,[],[f35,f51])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    r1_tsep_1(sK3,sK2) | ~spl6_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f49])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f152,plain,(
% 0.20/0.47    ( ! [X4] : (~r1_xboole_0(X4,u1_struct_0(sK2)) | r1_xboole_0(u1_struct_0(sK1),X4)) )),
% 0.20/0.47    inference(duplicate_literal_removal,[],[f149])).
% 0.20/0.47  fof(f149,plain,(
% 0.20/0.47    ( ! [X4] : (r1_xboole_0(u1_struct_0(sK1),X4) | ~r1_xboole_0(X4,u1_struct_0(sK2)) | r1_xboole_0(u1_struct_0(sK1),X4)) )),
% 0.20/0.47    inference(resolution,[],[f120,f82])).
% 0.20/0.47  fof(f82,plain,(
% 0.20/0.47    ( ! [X4,X5,X3] : (~r2_hidden(sK4(X3,X4),X5) | ~r1_xboole_0(X4,X5) | r1_xboole_0(X3,X4)) )),
% 0.20/0.47    inference(resolution,[],[f39,f41])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.47    inference(rectify,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f120,plain,(
% 0.20/0.47    ( ! [X3] : (r2_hidden(sK4(u1_struct_0(sK1),X3),u1_struct_0(sK2)) | r1_xboole_0(u1_struct_0(sK1),X3)) )),
% 0.20/0.47    inference(resolution,[],[f84,f102])).
% 0.20/0.47  fof(f102,plain,(
% 0.20/0.47    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))),
% 0.20/0.47    inference(resolution,[],[f97,f47])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.47  fof(f97,plain,(
% 0.20/0.47    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.20/0.47    inference(subsumption_resolution,[],[f93,f73])).
% 0.20/0.47  fof(f93,plain,(
% 0.20/0.47    ~l1_pre_topc(sK2) | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.20/0.47    inference(resolution,[],[f38,f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    m1_pre_topc(sK1,sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.20/0.47  fof(f84,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | r2_hidden(sK4(X0,X1),X2) | r1_xboole_0(X0,X1)) )),
% 0.20/0.47    inference(resolution,[],[f43,f40])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.47  fof(f90,plain,(
% 0.20/0.47    spl6_1 | ~spl6_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f89,f53,f49])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    spl6_2 <=> r1_tsep_1(sK2,sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.47  fof(f89,plain,(
% 0.20/0.47    r1_tsep_1(sK3,sK2) | ~spl6_2),
% 0.20/0.47    inference(subsumption_resolution,[],[f88,f76])).
% 0.20/0.47  fof(f88,plain,(
% 0.20/0.47    ~l1_struct_0(sK2) | r1_tsep_1(sK3,sK2) | ~spl6_2),
% 0.20/0.47    inference(subsumption_resolution,[],[f87,f74])).
% 0.20/0.47  fof(f87,plain,(
% 0.20/0.47    ~l1_struct_0(sK3) | ~l1_struct_0(sK2) | r1_tsep_1(sK3,sK2) | ~spl6_2),
% 0.20/0.47    inference(resolution,[],[f42,f55])).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    r1_tsep_1(sK2,sK3) | ~spl6_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f53])).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    ~spl6_3 | ~spl6_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f23,f62,f58])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ~r1_tsep_1(sK1,sK3) | ~r1_tsep_1(sK3,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    spl6_1 | spl6_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f22,f53,f49])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    r1_tsep_1(sK2,sK3) | r1_tsep_1(sK3,sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (14567)------------------------------
% 0.20/0.47  % (14567)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (14567)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (14567)Memory used [KB]: 5373
% 0.20/0.47  % (14567)Time elapsed: 0.054 s
% 0.20/0.47  % (14567)------------------------------
% 0.20/0.47  % (14567)------------------------------
% 0.20/0.47  % (14570)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.20/0.47  % (14560)Success in time 0.113 s
%------------------------------------------------------------------------------
