%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:31 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 178 expanded)
%              Number of leaves         :   16 (  49 expanded)
%              Depth                    :   10
%              Number of atoms          :  238 ( 874 expanded)
%              Number of equality atoms :   24 ( 100 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f613,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f120,f126,f149,f180,f258,f612])).

fof(f612,plain,
    ( spl3_1
    | ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f610])).

fof(f610,plain,
    ( $false
    | spl3_1
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f90,f416,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f416,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_1
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f71,f72,f259,f179])).

fof(f179,plain,
    ( ! [X2] :
        ( ~ v3_pre_topc(X2,sK0)
        | k1_xboole_0 = X2
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X2,sK1) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl3_6
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X2
        | ~ v3_pre_topc(X2,sK0)
        | ~ r1_tarski(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f259,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f44,f42,f96,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

fof(f96,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl3_1
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f42,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( v3_pre_topc(X2,X0)
                      & r1_tarski(X2,X1) )
                   => k1_xboole_0 = X2 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v3_pre_topc(X2,X0)
                    & r1_tarski(X2,X1) )
                 => k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tops_1)).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f72,plain,(
    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f43,f44,f42,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f43,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f71,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f44,f42,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f90,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f76,f71,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f76,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f42,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f258,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | spl3_4
    | ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f256])).

fof(f256,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | spl3_4
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f45,f227,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f227,plain,
    ( ~ r1_xboole_0(sK1,k1_xboole_0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | spl3_4
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f100,f125,f216,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

fof(f216,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f207,f181])).

fof(f181,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f44,f42,f95,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f95,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f207,plain,
    ( r1_tarski(sK2,k1_tops_1(sK0,sK1))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f44,f100,f119,f42,f148,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X1,k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

fof(f148,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl3_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f119,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl3_3
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f125,plain,
    ( k1_xboole_0 != sK2
    | spl3_4 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl3_4
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f100,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl3_2
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f45,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f180,plain,
    ( spl3_1
    | spl3_6 ),
    inference(avatar_split_clause,[],[f41,f178,f94])).

fof(f41,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X2,sK1)
      | ~ v3_pre_topc(X2,sK0)
      | k1_xboole_0 = X2
      | v2_tops_1(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f149,plain,
    ( ~ spl3_1
    | spl3_5 ),
    inference(avatar_split_clause,[],[f37,f146,f94])).

fof(f37,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f126,plain,
    ( ~ spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f40,f123,f94])).

fof(f40,plain,
    ( k1_xboole_0 != sK2
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f120,plain,
    ( ~ spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f39,f117,f94])).

fof(f39,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f101,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f38,f98,f94])).

fof(f38,plain,
    ( r1_tarski(sK2,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:10:24 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.44  % (3710)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.47  % (3727)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.48  % (3718)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.49  % (3709)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.49  % (3717)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.49  % (3729)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.49  % (3705)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.50  % (3708)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.50  % (3711)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.51  % (3731)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.51  % (3726)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.19/0.51  % (3706)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.51  % (3725)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.19/0.52  % (3720)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.52  % (3733)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.19/0.52  % (3728)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.52  % (3709)Refutation found. Thanks to Tanya!
% 0.19/0.52  % SZS status Theorem for theBenchmark
% 0.19/0.52  % (3712)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.52  % (3723)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.19/0.52  % (3730)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.52  % SZS output start Proof for theBenchmark
% 0.19/0.53  fof(f613,plain,(
% 0.19/0.53    $false),
% 0.19/0.53    inference(avatar_sat_refutation,[],[f101,f120,f126,f149,f180,f258,f612])).
% 0.19/0.53  fof(f612,plain,(
% 0.19/0.53    spl3_1 | ~spl3_6),
% 0.19/0.53    inference(avatar_contradiction_clause,[],[f610])).
% 0.19/0.53  fof(f610,plain,(
% 0.19/0.53    $false | (spl3_1 | ~spl3_6)),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f90,f416,f51])).
% 0.19/0.53  fof(f51,plain,(
% 0.19/0.53    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f13])).
% 0.19/0.53  fof(f13,axiom,(
% 0.19/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.19/0.53  fof(f416,plain,(
% 0.19/0.53    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl3_1 | ~spl3_6)),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f71,f72,f259,f179])).
% 0.19/0.53  fof(f179,plain,(
% 0.19/0.53    ( ! [X2] : (~v3_pre_topc(X2,sK0) | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X2,sK1)) ) | ~spl3_6),
% 0.19/0.53    inference(avatar_component_clause,[],[f178])).
% 0.19/0.53  fof(f178,plain,(
% 0.19/0.53    spl3_6 <=> ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X2 | ~v3_pre_topc(X2,sK0) | ~r1_tarski(X2,sK1))),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.19/0.53  fof(f259,plain,(
% 0.19/0.53    k1_xboole_0 != k1_tops_1(sK0,sK1) | spl3_1),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f44,f42,f96,f53])).
% 0.19/0.53  fof(f53,plain,(
% 0.19/0.53    ( ! [X0,X1] : (k1_xboole_0 != k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_tops_1(X1,X0)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f29])).
% 0.19/0.53  fof(f29,plain,(
% 0.19/0.53    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.53    inference(ennf_transformation,[],[f18])).
% 0.19/0.53  fof(f18,axiom,(
% 0.19/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).
% 0.19/0.53  fof(f96,plain,(
% 0.19/0.53    ~v2_tops_1(sK1,sK0) | spl3_1),
% 0.19/0.53    inference(avatar_component_clause,[],[f94])).
% 0.19/0.53  fof(f94,plain,(
% 0.19/0.53    spl3_1 <=> v2_tops_1(sK1,sK0)),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.19/0.53  fof(f42,plain,(
% 0.19/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.53    inference(cnf_transformation,[],[f22])).
% 0.19/0.53  fof(f22,plain,(
% 0.19/0.53    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.19/0.53    inference(flattening,[],[f21])).
% 0.19/0.53  fof(f21,plain,(
% 0.19/0.53    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : ((k1_xboole_0 = X2 | (~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.19/0.53    inference(ennf_transformation,[],[f20])).
% 0.19/0.53  fof(f20,negated_conjecture,(
% 0.19/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 0.19/0.53    inference(negated_conjecture,[],[f19])).
% 0.19/0.53  fof(f19,conjecture,(
% 0.19/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tops_1)).
% 0.19/0.53  fof(f44,plain,(
% 0.19/0.53    l1_pre_topc(sK0)),
% 0.19/0.53    inference(cnf_transformation,[],[f22])).
% 0.19/0.53  fof(f72,plain,(
% 0.19/0.53    v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f43,f44,f42,f48])).
% 0.19/0.53  fof(f48,plain,(
% 0.19/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f24])).
% 0.19/0.53  fof(f24,plain,(
% 0.19/0.53    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.53    inference(flattening,[],[f23])).
% 0.19/0.53  fof(f23,plain,(
% 0.19/0.53    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.19/0.53    inference(ennf_transformation,[],[f15])).
% 0.19/0.53  fof(f15,axiom,(
% 0.19/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 0.19/0.53  fof(f43,plain,(
% 0.19/0.53    v2_pre_topc(sK0)),
% 0.19/0.53    inference(cnf_transformation,[],[f22])).
% 0.19/0.53  fof(f71,plain,(
% 0.19/0.53    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f44,f42,f55])).
% 0.19/0.53  fof(f55,plain,(
% 0.19/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f30])).
% 0.19/0.53  fof(f30,plain,(
% 0.19/0.53    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.53    inference(ennf_transformation,[],[f16])).
% 0.19/0.53  fof(f16,axiom,(
% 0.19/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 0.19/0.53  fof(f90,plain,(
% 0.19/0.53    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f76,f71,f50])).
% 0.19/0.53  fof(f50,plain,(
% 0.19/0.53    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f28])).
% 0.19/0.53  fof(f28,plain,(
% 0.19/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.19/0.53    inference(flattening,[],[f27])).
% 0.19/0.53  fof(f27,plain,(
% 0.19/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.19/0.53    inference(ennf_transformation,[],[f2])).
% 0.19/0.53  fof(f2,axiom,(
% 0.19/0.53    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.19/0.53  fof(f76,plain,(
% 0.19/0.53    r1_tarski(sK1,u1_struct_0(sK0))),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f42,f52])).
% 0.19/0.53  fof(f52,plain,(
% 0.19/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.19/0.53    inference(cnf_transformation,[],[f13])).
% 0.19/0.53  fof(f258,plain,(
% 0.19/0.53    ~spl3_1 | ~spl3_2 | ~spl3_3 | spl3_4 | ~spl3_5),
% 0.19/0.53    inference(avatar_contradiction_clause,[],[f256])).
% 0.19/0.53  fof(f256,plain,(
% 0.19/0.53    $false | (~spl3_1 | ~spl3_2 | ~spl3_3 | spl3_4 | ~spl3_5)),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f45,f227,f56])).
% 0.19/0.53  fof(f56,plain,(
% 0.19/0.53    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 0.19/0.53    inference(cnf_transformation,[],[f8])).
% 0.19/0.53  fof(f8,axiom,(
% 0.19/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.19/0.53  fof(f227,plain,(
% 0.19/0.53    ~r1_xboole_0(sK1,k1_xboole_0) | (~spl3_1 | ~spl3_2 | ~spl3_3 | spl3_4 | ~spl3_5)),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f100,f125,f216,f60])).
% 0.19/0.53  fof(f60,plain,(
% 0.19/0.53    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1) | k1_xboole_0 = X0) )),
% 0.19/0.53    inference(cnf_transformation,[],[f33])).
% 0.19/0.53  fof(f33,plain,(
% 0.19/0.53    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.19/0.53    inference(flattening,[],[f32])).
% 0.19/0.53  fof(f32,plain,(
% 0.19/0.53    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.19/0.53    inference(ennf_transformation,[],[f7])).
% 0.19/0.53  fof(f7,axiom,(
% 0.19/0.53    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).
% 0.19/0.53  fof(f216,plain,(
% 0.19/0.53    r1_tarski(sK2,k1_xboole_0) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_5)),
% 0.19/0.53    inference(forward_demodulation,[],[f207,f181])).
% 0.19/0.53  fof(f181,plain,(
% 0.19/0.53    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl3_1),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f44,f42,f95,f54])).
% 0.19/0.53  fof(f54,plain,(
% 0.19/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f29])).
% 0.19/0.53  fof(f95,plain,(
% 0.19/0.53    v2_tops_1(sK1,sK0) | ~spl3_1),
% 0.19/0.53    inference(avatar_component_clause,[],[f94])).
% 0.19/0.53  fof(f207,plain,(
% 0.19/0.53    r1_tarski(sK2,k1_tops_1(sK0,sK1)) | (~spl3_2 | ~spl3_3 | ~spl3_5)),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f44,f100,f119,f42,f148,f49])).
% 0.19/0.53  fof(f49,plain,(
% 0.19/0.53    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~r1_tarski(X1,X2) | r1_tarski(X1,k1_tops_1(X0,X2))) )),
% 0.19/0.53    inference(cnf_transformation,[],[f26])).
% 0.19/0.53  fof(f26,plain,(
% 0.19/0.53    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.53    inference(flattening,[],[f25])).
% 0.19/0.53  fof(f25,plain,(
% 0.19/0.53    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.53    inference(ennf_transformation,[],[f17])).
% 0.19/0.53  fof(f17,axiom,(
% 0.19/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).
% 0.19/0.53  fof(f148,plain,(
% 0.19/0.53    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_5),
% 0.19/0.53    inference(avatar_component_clause,[],[f146])).
% 0.19/0.53  fof(f146,plain,(
% 0.19/0.53    spl3_5 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.19/0.53  fof(f119,plain,(
% 0.19/0.53    v3_pre_topc(sK2,sK0) | ~spl3_3),
% 0.19/0.53    inference(avatar_component_clause,[],[f117])).
% 0.19/0.53  fof(f117,plain,(
% 0.19/0.53    spl3_3 <=> v3_pre_topc(sK2,sK0)),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.19/0.53  fof(f125,plain,(
% 0.19/0.53    k1_xboole_0 != sK2 | spl3_4),
% 0.19/0.53    inference(avatar_component_clause,[],[f123])).
% 0.19/0.53  fof(f123,plain,(
% 0.19/0.53    spl3_4 <=> k1_xboole_0 = sK2),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.19/0.53  fof(f100,plain,(
% 0.19/0.53    r1_tarski(sK2,sK1) | ~spl3_2),
% 0.19/0.53    inference(avatar_component_clause,[],[f98])).
% 0.19/0.53  fof(f98,plain,(
% 0.19/0.53    spl3_2 <=> r1_tarski(sK2,sK1)),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.19/0.53  fof(f45,plain,(
% 0.19/0.53    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.19/0.53    inference(cnf_transformation,[],[f5])).
% 0.19/0.53  fof(f5,axiom,(
% 0.19/0.53    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.19/0.53  fof(f180,plain,(
% 0.19/0.53    spl3_1 | spl3_6),
% 0.19/0.53    inference(avatar_split_clause,[],[f41,f178,f94])).
% 0.19/0.53  fof(f41,plain,(
% 0.19/0.53    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X2,sK1) | ~v3_pre_topc(X2,sK0) | k1_xboole_0 = X2 | v2_tops_1(sK1,sK0)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f22])).
% 0.19/0.53  fof(f149,plain,(
% 0.19/0.53    ~spl3_1 | spl3_5),
% 0.19/0.53    inference(avatar_split_clause,[],[f37,f146,f94])).
% 0.19/0.53  fof(f37,plain,(
% 0.19/0.53    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_1(sK1,sK0)),
% 0.19/0.53    inference(cnf_transformation,[],[f22])).
% 0.19/0.53  fof(f126,plain,(
% 0.19/0.53    ~spl3_1 | ~spl3_4),
% 0.19/0.53    inference(avatar_split_clause,[],[f40,f123,f94])).
% 0.19/0.53  fof(f40,plain,(
% 0.19/0.53    k1_xboole_0 != sK2 | ~v2_tops_1(sK1,sK0)),
% 0.19/0.53    inference(cnf_transformation,[],[f22])).
% 0.19/0.53  fof(f120,plain,(
% 0.19/0.53    ~spl3_1 | spl3_3),
% 0.19/0.53    inference(avatar_split_clause,[],[f39,f117,f94])).
% 0.19/0.53  fof(f39,plain,(
% 0.19/0.53    v3_pre_topc(sK2,sK0) | ~v2_tops_1(sK1,sK0)),
% 0.19/0.53    inference(cnf_transformation,[],[f22])).
% 0.19/0.53  fof(f101,plain,(
% 0.19/0.53    ~spl3_1 | spl3_2),
% 0.19/0.53    inference(avatar_split_clause,[],[f38,f98,f94])).
% 0.19/0.53  fof(f38,plain,(
% 0.19/0.53    r1_tarski(sK2,sK1) | ~v2_tops_1(sK1,sK0)),
% 0.19/0.53    inference(cnf_transformation,[],[f22])).
% 0.19/0.53  % SZS output end Proof for theBenchmark
% 0.19/0.53  % (3709)------------------------------
% 0.19/0.53  % (3709)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (3709)Termination reason: Refutation
% 0.19/0.53  
% 0.19/0.53  % (3709)Memory used [KB]: 6396
% 0.19/0.53  % (3709)Time elapsed: 0.124 s
% 0.19/0.53  % (3709)------------------------------
% 0.19/0.53  % (3709)------------------------------
% 0.19/0.53  % (3707)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.41/0.53  % (3701)Success in time 0.186 s
%------------------------------------------------------------------------------
