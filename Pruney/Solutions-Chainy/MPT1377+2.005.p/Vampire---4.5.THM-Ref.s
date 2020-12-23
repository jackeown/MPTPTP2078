%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:54 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 313 expanded)
%              Number of leaves         :   30 ( 114 expanded)
%              Depth                    :   16
%              Number of atoms          :  580 (1212 expanded)
%              Number of equality atoms :   33 (  77 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f874,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f74,f95,f115,f134,f153,f214,f219,f239,f505,f643,f801,f847,f857,f864,f873])).

fof(f873,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_35
    | spl2_36 ),
    inference(avatar_contradiction_clause,[],[f872])).

fof(f872,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_35
    | spl2_36 ),
    inference(subsumption_resolution,[],[f871,f824])).

fof(f824,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_5
    | ~ spl2_35 ),
    inference(superposition,[],[f84,f800])).

fof(f800,plain,
    ( u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_35 ),
    inference(avatar_component_clause,[],[f798])).

fof(f798,plain,
    ( spl2_35
  <=> u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).

fof(f84,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl2_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f871,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_7
    | spl2_36 ),
    inference(subsumption_resolution,[],[f868,f69])).

fof(f69,plain,
    ( v2_compts_1(sK1,sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl2_2
  <=> v2_compts_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f868,plain,
    ( ~ v2_compts_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_1
    | ~ spl2_7
    | spl2_36 ),
    inference(resolution,[],[f845,f124])).

fof(f124,plain,
    ( ! [X0] :
        ( v2_compts_1(X0,k1_pre_topc(sK0,u1_struct_0(sK0)))
        | ~ v2_compts_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(duplicate_literal_removal,[],[f123])).

fof(f123,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_compts_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_compts_1(X0,k1_pre_topc(sK0,u1_struct_0(sK0))) )
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(forward_demodulation,[],[f122,f105])).

fof(f105,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0)))
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f64,f60,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

fof(f60,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f43,f42])).

fof(f42,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f43,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f64,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f62])).

% (27043)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
fof(f62,plain,
    ( spl2_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f122,plain,
    ( ! [X0] :
        ( ~ v2_compts_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0)))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_compts_1(X0,k1_pre_topc(sK0,u1_struct_0(sK0))) )
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f117,f64])).

fof(f117,plain,
    ( ! [X0] :
        ( ~ v2_compts_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0)))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_compts_1(X0,k1_pre_topc(sK0,u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl2_7 ),
    inference(resolution,[],[f114,f59])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_compts_1(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_compts_1(X3,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_compts_1(X3,X1)
      | ~ v2_compts_1(X2,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v2_compts_1(X2,X0)
                      | ~ v2_compts_1(X3,X1) )
                    & ( v2_compts_1(X3,X1)
                      | ~ v2_compts_1(X2,X0) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v2_compts_1(X2,X0)
                  <=> v2_compts_1(X3,X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v2_compts_1(X2,X0)
                  <=> v2_compts_1(X3,X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( X2 = X3
                   => ( v2_compts_1(X2,X0)
                    <=> v2_compts_1(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_compts_1)).

fof(f114,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),sK0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl2_7
  <=> m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f845,plain,
    ( ~ v2_compts_1(sK1,k1_pre_topc(sK0,u1_struct_0(sK0)))
    | spl2_36 ),
    inference(avatar_component_clause,[],[f844])).

fof(f844,plain,
    ( spl2_36
  <=> v2_compts_1(sK1,k1_pre_topc(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).

fof(f864,plain,
    ( ~ spl2_1
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_13
    | ~ spl2_35
    | ~ spl2_36 ),
    inference(avatar_contradiction_clause,[],[f863])).

fof(f863,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_13
    | ~ spl2_35
    | ~ spl2_36 ),
    inference(subsumption_resolution,[],[f862,f853])).

fof(f853,plain,
    ( v2_compts_1(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_35
    | ~ spl2_36 ),
    inference(subsumption_resolution,[],[f850,f824])).

fof(f850,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_compts_1(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_7
    | ~ spl2_36 ),
    inference(resolution,[],[f846,f127])).

fof(f127,plain,
    ( ! [X1] :
        ( ~ v2_compts_1(X1,k1_pre_topc(sK0,u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_compts_1(X1,sK0) )
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_compts_1(X1,k1_pre_topc(sK0,u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_compts_1(X1,sK0) )
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(forward_demodulation,[],[f125,f105])).

fof(f125,plain,
    ( ! [X1] :
        ( ~ v2_compts_1(X1,k1_pre_topc(sK0,u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0)))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_compts_1(X1,sK0) )
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f118,f64])).

fof(f118,plain,
    ( ! [X1] :
        ( ~ v2_compts_1(X1,k1_pre_topc(sK0,u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0)))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_compts_1(X1,sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl2_7 ),
    inference(resolution,[],[f114,f58])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_compts_1(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_compts_1(X3,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_compts_1(X2,X0)
      | ~ v2_compts_1(X3,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f846,plain,
    ( v2_compts_1(sK1,k1_pre_topc(sK0,u1_struct_0(sK0)))
    | ~ spl2_36 ),
    inference(avatar_component_clause,[],[f844])).

fof(f862,plain,
    ( ~ v2_compts_1(sK1,sK0)
    | ~ spl2_5
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_13
    | ~ spl2_35
    | ~ spl2_36 ),
    inference(subsumption_resolution,[],[f861,f824])).

fof(f861,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_compts_1(sK1,sK0)
    | ~ spl2_5
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_13
    | ~ spl2_35
    | ~ spl2_36 ),
    inference(subsumption_resolution,[],[f860,f859])).

fof(f859,plain,
    ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_5
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_13
    | ~ spl2_35
    | ~ spl2_36 ),
    inference(subsumption_resolution,[],[f858,f84])).

fof(f858,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_5
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_13
    | ~ spl2_35
    | ~ spl2_36 ),
    inference(subsumption_resolution,[],[f849,f824])).

fof(f849,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_13
    | ~ spl2_36 ),
    inference(resolution,[],[f846,f257])).

fof(f257,plain,
    ( ! [X1] :
        ( ~ v2_compts_1(X1,k1_pre_topc(sK0,u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f256,f152])).

fof(f152,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0)))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl2_9
  <=> u1_struct_0(sK0) = u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f256,plain,
    ( ! [X1] :
        ( ~ v2_compts_1(X1,k1_pre_topc(sK0,u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0)))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl2_11
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f250,f213])).

fof(f213,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f211])).

fof(f211,plain,
    ( spl2_11
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f250,plain,
    ( ! [X1] :
        ( ~ v2_compts_1(X1,k1_pre_topc(sK0,u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0)))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl2_13 ),
    inference(resolution,[],[f238,f58])).

fof(f238,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f236])).

fof(f236,plain,
    ( spl2_13
  <=> m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f860,plain,
    ( ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_compts_1(sK1,sK0)
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f41,f84])).

fof(f41,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
      | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_compts_1(sK1,sK0) )
    & ( ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        & v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
      | ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        & v2_compts_1(sK1,sK0) ) )
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f32,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v2_compts_1(X1,X0) )
            & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
                & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
              | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                & v2_compts_1(X1,X0) ) ) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
            | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
            | ~ v2_compts_1(X1,sK0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
              & v2_compts_1(X1,sK0) ) ) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
          | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          | ~ v2_compts_1(X1,sK0) )
        & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
            & v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
          | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
            & v2_compts_1(X1,sK0) ) ) )
   => ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_compts_1(sK1,sK0) )
      & ( ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
          & v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
        | ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
          & v2_compts_1(sK1,sK0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v2_compts_1(X1,X0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) ) ) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v2_compts_1(X1,X0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) ) ) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_compts_1(X1,X0) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_compts_1(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_compts_1)).

fof(f857,plain,
    ( u1_struct_0(sK0) != u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f847,plain,
    ( spl2_36
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_13
    | ~ spl2_35 ),
    inference(avatar_split_clause,[],[f835,f798,f236,f211,f150,f82,f71,f844])).

fof(f71,plain,
    ( spl2_3
  <=> v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f835,plain,
    ( v2_compts_1(sK1,k1_pre_topc(sK0,u1_struct_0(sK0)))
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_13
    | ~ spl2_35 ),
    inference(subsumption_resolution,[],[f738,f824])).

fof(f738,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_compts_1(sK1,k1_pre_topc(sK0,u1_struct_0(sK0)))
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f737,f84])).

fof(f737,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | v2_compts_1(sK1,k1_pre_topc(sK0,u1_struct_0(sK0)))
    | ~ spl2_3
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_13 ),
    inference(resolution,[],[f255,f73])).

fof(f73,plain,
    ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f255,plain,
    ( ! [X0] :
        ( ~ v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | v2_compts_1(X0,k1_pre_topc(sK0,u1_struct_0(sK0))) )
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f254,f152])).

fof(f254,plain,
    ( ! [X0] :
        ( ~ v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0)))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | v2_compts_1(X0,k1_pre_topc(sK0,u1_struct_0(sK0))) )
    | ~ spl2_11
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f249,f213])).

fof(f249,plain,
    ( ! [X0] :
        ( ~ v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0)))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | v2_compts_1(X0,k1_pre_topc(sK0,u1_struct_0(sK0)))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl2_13 ),
    inference(resolution,[],[f238,f59])).

fof(f801,plain,
    ( spl2_35
    | ~ spl2_26
    | ~ spl2_28 ),
    inference(avatar_split_clause,[],[f652,f640,f502,f798])).

fof(f502,plain,
    ( spl2_26
  <=> m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f640,plain,
    ( spl2_28
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f652,plain,
    ( u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_26
    | ~ spl2_28 ),
    inference(unit_resulting_resolution,[],[f504,f642,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f642,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f640])).

fof(f504,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f502])).

fof(f643,plain,
    ( spl2_28
    | ~ spl2_11
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f233,f216,f211,f640])).

fof(f216,plain,
    ( spl2_12
  <=> v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f233,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl2_11
    | ~ spl2_12 ),
    inference(unit_resulting_resolution,[],[f213,f218,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f218,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f216])).

fof(f505,plain,
    ( spl2_26
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f220,f211,f502])).

fof(f220,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ spl2_11 ),
    inference(unit_resulting_resolution,[],[f213,f44])).

fof(f44,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f239,plain,
    ( spl2_13
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f129,f112,f62,f236])).

fof(f129,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f128,f116])).

fof(f116,plain,
    ( l1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)))
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f64,f114,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f128,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)))
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f119,f64])).

fof(f119,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)))
    | ~ spl2_7 ),
    inference(resolution,[],[f114,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f219,plain,
    ( spl2_12
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f136,f131,f216])).

fof(f131,plain,
    ( spl2_8
  <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f136,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_8 ),
    inference(unit_resulting_resolution,[],[f133,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f133,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f131])).

fof(f214,plain,
    ( spl2_11
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f135,f131,f211])).

fof(f135,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_8 ),
    inference(unit_resulting_resolution,[],[f133,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f153,plain,
    ( spl2_9
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f105,f62,f150])).

fof(f134,plain,
    ( spl2_8
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f88,f62,f131])).

fof(f88,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f64,f44])).

fof(f115,plain,
    ( spl2_7
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f98,f62,f112])).

fof(f98,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),sK0)
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f64,f60,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f95,plain,
    ( spl2_4
    | spl2_5 ),
    inference(avatar_split_clause,[],[f40,f82,f77])).

fof(f77,plain,
    ( spl2_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f40,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f74,plain,
    ( spl2_2
    | spl2_3 ),
    inference(avatar_split_clause,[],[f37,f71,f67])).

fof(f37,plain,
    ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f65,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f36,f62])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n003.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:17:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (27026)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.52  % (27034)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.55  % (27046)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.55  % (27029)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.55  % (27024)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.55  % (27038)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.55  % (27024)Refutation not found, incomplete strategy% (27024)------------------------------
% 0.22/0.55  % (27024)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (27024)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (27024)Memory used [KB]: 10618
% 0.22/0.55  % (27024)Time elapsed: 0.122 s
% 0.22/0.55  % (27024)------------------------------
% 0.22/0.55  % (27024)------------------------------
% 1.55/0.56  % (27030)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.55/0.57  % (27047)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.55/0.57  % (27027)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.55/0.57  % (27033)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.55/0.57  % (27028)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.61/0.57  % (27029)Refutation not found, incomplete strategy% (27029)------------------------------
% 1.61/0.57  % (27029)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.57  % (27029)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.57  
% 1.61/0.57  % (27029)Memory used [KB]: 10746
% 1.61/0.57  % (27029)Time elapsed: 0.150 s
% 1.61/0.57  % (27029)------------------------------
% 1.61/0.57  % (27029)------------------------------
% 1.61/0.58  % (27032)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.61/0.58  % (27037)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.61/0.58  % (27044)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.61/0.58  % (27025)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.61/0.59  % (27042)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.61/0.59  % (27046)Refutation found. Thanks to Tanya!
% 1.61/0.59  % SZS status Theorem for theBenchmark
% 1.61/0.59  % (27039)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.61/0.59  % (27035)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.61/0.59  % (27041)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.61/0.59  % (27031)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.61/0.59  % SZS output start Proof for theBenchmark
% 1.61/0.59  fof(f874,plain,(
% 1.61/0.59    $false),
% 1.61/0.59    inference(avatar_sat_refutation,[],[f65,f74,f95,f115,f134,f153,f214,f219,f239,f505,f643,f801,f847,f857,f864,f873])).
% 1.61/0.59  fof(f873,plain,(
% 1.61/0.59    ~spl2_1 | ~spl2_2 | ~spl2_5 | ~spl2_7 | ~spl2_35 | spl2_36),
% 1.61/0.59    inference(avatar_contradiction_clause,[],[f872])).
% 1.61/0.59  fof(f872,plain,(
% 1.61/0.59    $false | (~spl2_1 | ~spl2_2 | ~spl2_5 | ~spl2_7 | ~spl2_35 | spl2_36)),
% 1.61/0.59    inference(subsumption_resolution,[],[f871,f824])).
% 1.61/0.59  fof(f824,plain,(
% 1.61/0.59    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_5 | ~spl2_35)),
% 1.61/0.59    inference(superposition,[],[f84,f800])).
% 1.61/0.59  fof(f800,plain,(
% 1.61/0.59    u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_35),
% 1.61/0.59    inference(avatar_component_clause,[],[f798])).
% 1.61/0.59  fof(f798,plain,(
% 1.61/0.59    spl2_35 <=> u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.61/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).
% 1.61/0.59  fof(f84,plain,(
% 1.61/0.59    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~spl2_5),
% 1.61/0.59    inference(avatar_component_clause,[],[f82])).
% 1.61/0.59  fof(f82,plain,(
% 1.61/0.59    spl2_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))),
% 1.61/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.61/0.59  fof(f871,plain,(
% 1.61/0.59    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_1 | ~spl2_2 | ~spl2_7 | spl2_36)),
% 1.61/0.59    inference(subsumption_resolution,[],[f868,f69])).
% 1.61/0.59  fof(f69,plain,(
% 1.61/0.59    v2_compts_1(sK1,sK0) | ~spl2_2),
% 1.61/0.59    inference(avatar_component_clause,[],[f67])).
% 1.61/0.59  fof(f67,plain,(
% 1.61/0.59    spl2_2 <=> v2_compts_1(sK1,sK0)),
% 1.61/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.61/0.59  fof(f868,plain,(
% 1.61/0.59    ~v2_compts_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_1 | ~spl2_7 | spl2_36)),
% 1.61/0.59    inference(resolution,[],[f845,f124])).
% 1.61/0.59  fof(f124,plain,(
% 1.61/0.59    ( ! [X0] : (v2_compts_1(X0,k1_pre_topc(sK0,u1_struct_0(sK0))) | ~v2_compts_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl2_1 | ~spl2_7)),
% 1.61/0.59    inference(duplicate_literal_removal,[],[f123])).
% 1.61/0.59  fof(f123,plain,(
% 1.61/0.59    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_compts_1(X0,k1_pre_topc(sK0,u1_struct_0(sK0)))) ) | (~spl2_1 | ~spl2_7)),
% 1.61/0.59    inference(forward_demodulation,[],[f122,f105])).
% 1.61/0.59  fof(f105,plain,(
% 1.61/0.59    u1_struct_0(sK0) = u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0))) | ~spl2_1),
% 1.61/0.59    inference(unit_resulting_resolution,[],[f64,f60,f51])).
% 1.61/0.59  fof(f51,plain,(
% 1.61/0.59    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(k1_pre_topc(X0,X1)) = X1) )),
% 1.61/0.59    inference(cnf_transformation,[],[f24])).
% 1.61/0.59  fof(f24,plain,(
% 1.61/0.59    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.61/0.59    inference(ennf_transformation,[],[f9])).
% 1.61/0.59  fof(f9,axiom,(
% 1.61/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).
% 1.61/0.59  fof(f60,plain,(
% 1.61/0.59    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.61/0.59    inference(forward_demodulation,[],[f43,f42])).
% 1.61/0.59  fof(f42,plain,(
% 1.61/0.59    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.61/0.59    inference(cnf_transformation,[],[f1])).
% 1.61/0.59  fof(f1,axiom,(
% 1.61/0.59    ! [X0] : k2_subset_1(X0) = X0),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.61/0.59  fof(f43,plain,(
% 1.61/0.59    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.61/0.59    inference(cnf_transformation,[],[f2])).
% 1.61/0.59  fof(f2,axiom,(
% 1.61/0.59    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.61/0.59  fof(f64,plain,(
% 1.61/0.59    l1_pre_topc(sK0) | ~spl2_1),
% 1.61/0.59    inference(avatar_component_clause,[],[f62])).
% 1.61/0.59  % (27043)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.61/0.59  fof(f62,plain,(
% 1.61/0.59    spl2_1 <=> l1_pre_topc(sK0)),
% 1.61/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.61/0.59  fof(f122,plain,(
% 1.61/0.59    ( ! [X0] : (~v2_compts_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0))))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_compts_1(X0,k1_pre_topc(sK0,u1_struct_0(sK0)))) ) | (~spl2_1 | ~spl2_7)),
% 1.61/0.59    inference(subsumption_resolution,[],[f117,f64])).
% 1.61/0.59  fof(f117,plain,(
% 1.61/0.59    ( ! [X0] : (~v2_compts_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0))))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_compts_1(X0,k1_pre_topc(sK0,u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl2_7),
% 1.61/0.59    inference(resolution,[],[f114,f59])).
% 1.61/0.59  fof(f59,plain,(
% 1.61/0.59    ( ! [X0,X3,X1] : (~m1_pre_topc(X1,X0) | ~v2_compts_1(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v2_compts_1(X3,X1) | ~l1_pre_topc(X0)) )),
% 1.61/0.59    inference(equality_resolution,[],[f49])).
% 1.61/0.59  fof(f49,plain,(
% 1.61/0.59    ( ! [X2,X0,X3,X1] : (v2_compts_1(X3,X1) | ~v2_compts_1(X2,X0) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.61/0.59    inference(cnf_transformation,[],[f35])).
% 1.61/0.59  fof(f35,plain,(
% 1.61/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v2_compts_1(X2,X0) | ~v2_compts_1(X3,X1)) & (v2_compts_1(X3,X1) | ~v2_compts_1(X2,X0))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.61/0.59    inference(nnf_transformation,[],[f23])).
% 1.61/0.59  fof(f23,plain,(
% 1.61/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v2_compts_1(X2,X0) <=> v2_compts_1(X3,X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.61/0.59    inference(flattening,[],[f22])).
% 1.61/0.59  fof(f22,plain,(
% 1.61/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v2_compts_1(X2,X0) <=> v2_compts_1(X3,X1)) | X2 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.61/0.59    inference(ennf_transformation,[],[f11])).
% 1.61/0.59  fof(f11,axiom,(
% 1.61/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (X2 = X3 => (v2_compts_1(X2,X0) <=> v2_compts_1(X3,X1)))))))),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_compts_1)).
% 1.61/0.59  fof(f114,plain,(
% 1.61/0.59    m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),sK0) | ~spl2_7),
% 1.61/0.59    inference(avatar_component_clause,[],[f112])).
% 1.61/0.59  fof(f112,plain,(
% 1.61/0.59    spl2_7 <=> m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),sK0)),
% 1.61/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 1.61/0.59  fof(f845,plain,(
% 1.61/0.59    ~v2_compts_1(sK1,k1_pre_topc(sK0,u1_struct_0(sK0))) | spl2_36),
% 1.61/0.59    inference(avatar_component_clause,[],[f844])).
% 1.61/0.59  fof(f844,plain,(
% 1.61/0.59    spl2_36 <=> v2_compts_1(sK1,k1_pre_topc(sK0,u1_struct_0(sK0)))),
% 1.61/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).
% 1.61/0.59  fof(f864,plain,(
% 1.61/0.59    ~spl2_1 | ~spl2_5 | ~spl2_7 | ~spl2_9 | ~spl2_11 | ~spl2_13 | ~spl2_35 | ~spl2_36),
% 1.61/0.59    inference(avatar_contradiction_clause,[],[f863])).
% 1.61/0.59  fof(f863,plain,(
% 1.61/0.59    $false | (~spl2_1 | ~spl2_5 | ~spl2_7 | ~spl2_9 | ~spl2_11 | ~spl2_13 | ~spl2_35 | ~spl2_36)),
% 1.61/0.59    inference(subsumption_resolution,[],[f862,f853])).
% 1.61/0.59  fof(f853,plain,(
% 1.61/0.59    v2_compts_1(sK1,sK0) | (~spl2_1 | ~spl2_5 | ~spl2_7 | ~spl2_35 | ~spl2_36)),
% 1.61/0.59    inference(subsumption_resolution,[],[f850,f824])).
% 1.61/0.59  fof(f850,plain,(
% 1.61/0.59    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_compts_1(sK1,sK0) | (~spl2_1 | ~spl2_7 | ~spl2_36)),
% 1.61/0.59    inference(resolution,[],[f846,f127])).
% 1.61/0.59  fof(f127,plain,(
% 1.61/0.59    ( ! [X1] : (~v2_compts_1(X1,k1_pre_topc(sK0,u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_compts_1(X1,sK0)) ) | (~spl2_1 | ~spl2_7)),
% 1.61/0.59    inference(duplicate_literal_removal,[],[f126])).
% 1.61/0.59  fof(f126,plain,(
% 1.61/0.59    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(X1,k1_pre_topc(sK0,u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_compts_1(X1,sK0)) ) | (~spl2_1 | ~spl2_7)),
% 1.61/0.59    inference(forward_demodulation,[],[f125,f105])).
% 1.61/0.59  fof(f125,plain,(
% 1.61/0.59    ( ! [X1] : (~v2_compts_1(X1,k1_pre_topc(sK0,u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_compts_1(X1,sK0)) ) | (~spl2_1 | ~spl2_7)),
% 1.61/0.59    inference(subsumption_resolution,[],[f118,f64])).
% 1.61/0.59  fof(f118,plain,(
% 1.61/0.59    ( ! [X1] : (~v2_compts_1(X1,k1_pre_topc(sK0,u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_compts_1(X1,sK0) | ~l1_pre_topc(sK0)) ) | ~spl2_7),
% 1.61/0.59    inference(resolution,[],[f114,f58])).
% 1.61/0.59  fof(f58,plain,(
% 1.61/0.59    ( ! [X0,X3,X1] : (~m1_pre_topc(X1,X0) | ~v2_compts_1(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v2_compts_1(X3,X0) | ~l1_pre_topc(X0)) )),
% 1.61/0.59    inference(equality_resolution,[],[f50])).
% 1.61/0.59  fof(f50,plain,(
% 1.61/0.59    ( ! [X2,X0,X3,X1] : (v2_compts_1(X2,X0) | ~v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.61/0.59    inference(cnf_transformation,[],[f35])).
% 1.61/0.59  fof(f846,plain,(
% 1.61/0.59    v2_compts_1(sK1,k1_pre_topc(sK0,u1_struct_0(sK0))) | ~spl2_36),
% 1.61/0.59    inference(avatar_component_clause,[],[f844])).
% 1.61/0.59  fof(f862,plain,(
% 1.61/0.59    ~v2_compts_1(sK1,sK0) | (~spl2_5 | ~spl2_9 | ~spl2_11 | ~spl2_13 | ~spl2_35 | ~spl2_36)),
% 1.61/0.59    inference(subsumption_resolution,[],[f861,f824])).
% 1.61/0.59  fof(f861,plain,(
% 1.61/0.59    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(sK1,sK0) | (~spl2_5 | ~spl2_9 | ~spl2_11 | ~spl2_13 | ~spl2_35 | ~spl2_36)),
% 1.61/0.59    inference(subsumption_resolution,[],[f860,f859])).
% 1.61/0.59  fof(f859,plain,(
% 1.61/0.59    v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl2_5 | ~spl2_9 | ~spl2_11 | ~spl2_13 | ~spl2_35 | ~spl2_36)),
% 1.61/0.59    inference(subsumption_resolution,[],[f858,f84])).
% 1.61/0.59  fof(f858,plain,(
% 1.61/0.59    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl2_5 | ~spl2_9 | ~spl2_11 | ~spl2_13 | ~spl2_35 | ~spl2_36)),
% 1.61/0.59    inference(subsumption_resolution,[],[f849,f824])).
% 1.61/0.59  fof(f849,plain,(
% 1.61/0.59    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl2_9 | ~spl2_11 | ~spl2_13 | ~spl2_36)),
% 1.61/0.59    inference(resolution,[],[f846,f257])).
% 1.61/0.59  fof(f257,plain,(
% 1.61/0.59    ( ! [X1] : (~v2_compts_1(X1,k1_pre_topc(sK0,u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ) | (~spl2_9 | ~spl2_11 | ~spl2_13)),
% 1.61/0.59    inference(forward_demodulation,[],[f256,f152])).
% 1.61/0.59  fof(f152,plain,(
% 1.61/0.59    u1_struct_0(sK0) = u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0))) | ~spl2_9),
% 1.61/0.59    inference(avatar_component_clause,[],[f150])).
% 1.61/0.59  fof(f150,plain,(
% 1.61/0.59    spl2_9 <=> u1_struct_0(sK0) = u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0)))),
% 1.61/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 1.61/0.59  fof(f256,plain,(
% 1.61/0.59    ( ! [X1] : (~v2_compts_1(X1,k1_pre_topc(sK0,u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ) | (~spl2_11 | ~spl2_13)),
% 1.61/0.59    inference(subsumption_resolution,[],[f250,f213])).
% 1.61/0.59  fof(f213,plain,(
% 1.61/0.59    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_11),
% 1.61/0.59    inference(avatar_component_clause,[],[f211])).
% 1.61/0.59  fof(f211,plain,(
% 1.61/0.59    spl2_11 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.61/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 1.61/0.59  fof(f250,plain,(
% 1.61/0.59    ( ! [X1] : (~v2_compts_1(X1,k1_pre_topc(sK0,u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ) | ~spl2_13),
% 1.61/0.59    inference(resolution,[],[f238,f58])).
% 1.61/0.59  fof(f238,plain,(
% 1.61/0.59    m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_13),
% 1.61/0.59    inference(avatar_component_clause,[],[f236])).
% 1.61/0.59  fof(f236,plain,(
% 1.61/0.59    spl2_13 <=> m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.61/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 1.61/0.59  fof(f860,plain,(
% 1.61/0.59    ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(sK1,sK0) | ~spl2_5),
% 1.61/0.59    inference(subsumption_resolution,[],[f41,f84])).
% 1.61/0.59  fof(f41,plain,(
% 1.61/0.59    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(sK1,sK0)),
% 1.61/0.59    inference(cnf_transformation,[],[f33])).
% 1.61/0.59  fof(f33,plain,(
% 1.61/0.59    ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(sK1,sK0)) & ((m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) & v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v2_compts_1(sK1,sK0)))) & l1_pre_topc(sK0)),
% 1.61/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f32,f31])).
% 1.61/0.59  fof(f31,plain,(
% 1.61/0.59    ? [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(X1,sK0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v2_compts_1(X1,sK0)))) & l1_pre_topc(sK0))),
% 1.61/0.59    introduced(choice_axiom,[])).
% 1.61/0.59  fof(f32,plain,(
% 1.61/0.59    ? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(X1,sK0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v2_compts_1(X1,sK0)))) => ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(sK1,sK0)) & ((m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) & v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v2_compts_1(sK1,sK0))))),
% 1.61/0.59    introduced(choice_axiom,[])).
% 1.61/0.59  fof(f30,plain,(
% 1.61/0.59    ? [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)))) & l1_pre_topc(X0))),
% 1.61/0.59    inference(flattening,[],[f29])).
% 1.61/0.60  fof(f29,plain,(
% 1.61/0.60    ? [X0] : (? [X1] : (((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)))) & l1_pre_topc(X0))),
% 1.61/0.60    inference(nnf_transformation,[],[f16])).
% 1.61/0.60  fof(f16,plain,(
% 1.61/0.60    ? [X0] : (? [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <~> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & l1_pre_topc(X0))),
% 1.61/0.60    inference(ennf_transformation,[],[f15])).
% 1.61/0.60  fof(f15,plain,(
% 1.61/0.60    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 1.61/0.60    inference(pure_predicate_removal,[],[f14])).
% 1.61/0.60  fof(f14,plain,(
% 1.61/0.60    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 1.61/0.60    inference(pure_predicate_removal,[],[f13])).
% 1.61/0.60  fof(f13,negated_conjecture,(
% 1.61/0.60    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 1.61/0.60    inference(negated_conjecture,[],[f12])).
% 1.61/0.60  fof(f12,conjecture,(
% 1.61/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 1.61/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_compts_1)).
% 1.61/0.60  fof(f857,plain,(
% 1.61/0.60    u1_struct_0(sK0) != u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.61/0.60    introduced(theory_tautology_sat_conflict,[])).
% 1.61/0.60  fof(f847,plain,(
% 1.61/0.60    spl2_36 | ~spl2_3 | ~spl2_5 | ~spl2_9 | ~spl2_11 | ~spl2_13 | ~spl2_35),
% 1.61/0.60    inference(avatar_split_clause,[],[f835,f798,f236,f211,f150,f82,f71,f844])).
% 1.61/0.60  fof(f71,plain,(
% 1.61/0.60    spl2_3 <=> v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.61/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.61/0.60  fof(f835,plain,(
% 1.61/0.60    v2_compts_1(sK1,k1_pre_topc(sK0,u1_struct_0(sK0))) | (~spl2_3 | ~spl2_5 | ~spl2_9 | ~spl2_11 | ~spl2_13 | ~spl2_35)),
% 1.61/0.60    inference(subsumption_resolution,[],[f738,f824])).
% 1.61/0.60  fof(f738,plain,(
% 1.61/0.60    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_compts_1(sK1,k1_pre_topc(sK0,u1_struct_0(sK0))) | (~spl2_3 | ~spl2_5 | ~spl2_9 | ~spl2_11 | ~spl2_13)),
% 1.61/0.60    inference(subsumption_resolution,[],[f737,f84])).
% 1.61/0.60  fof(f737,plain,(
% 1.61/0.60    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | v2_compts_1(sK1,k1_pre_topc(sK0,u1_struct_0(sK0))) | (~spl2_3 | ~spl2_9 | ~spl2_11 | ~spl2_13)),
% 1.61/0.60    inference(resolution,[],[f255,f73])).
% 1.61/0.60  fof(f73,plain,(
% 1.61/0.60    v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_3),
% 1.61/0.60    inference(avatar_component_clause,[],[f71])).
% 1.61/0.60  fof(f255,plain,(
% 1.61/0.60    ( ! [X0] : (~v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | v2_compts_1(X0,k1_pre_topc(sK0,u1_struct_0(sK0)))) ) | (~spl2_9 | ~spl2_11 | ~spl2_13)),
% 1.61/0.60    inference(forward_demodulation,[],[f254,f152])).
% 1.61/0.60  fof(f254,plain,(
% 1.61/0.60    ( ! [X0] : (~v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0))))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | v2_compts_1(X0,k1_pre_topc(sK0,u1_struct_0(sK0)))) ) | (~spl2_11 | ~spl2_13)),
% 1.61/0.60    inference(subsumption_resolution,[],[f249,f213])).
% 1.61/0.60  fof(f249,plain,(
% 1.61/0.60    ( ! [X0] : (~v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0))))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | v2_compts_1(X0,k1_pre_topc(sK0,u1_struct_0(sK0))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ) | ~spl2_13),
% 1.61/0.60    inference(resolution,[],[f238,f59])).
% 1.61/0.60  fof(f801,plain,(
% 1.61/0.60    spl2_35 | ~spl2_26 | ~spl2_28),
% 1.61/0.60    inference(avatar_split_clause,[],[f652,f640,f502,f798])).
% 1.61/0.60  fof(f502,plain,(
% 1.61/0.60    spl2_26 <=> m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))),
% 1.61/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 1.61/0.60  fof(f640,plain,(
% 1.61/0.60    spl2_28 <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 1.61/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 1.61/0.60  fof(f652,plain,(
% 1.61/0.60    u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl2_26 | ~spl2_28)),
% 1.61/0.60    inference(unit_resulting_resolution,[],[f504,f642,f54])).
% 1.61/0.60  fof(f54,plain,(
% 1.61/0.60    ( ! [X2,X0,X3,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X0 = X2 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.61/0.60    inference(cnf_transformation,[],[f26])).
% 1.61/0.60  fof(f26,plain,(
% 1.61/0.60    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.61/0.60    inference(ennf_transformation,[],[f8])).
% 1.61/0.60  fof(f8,axiom,(
% 1.61/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 1.61/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).
% 1.61/0.60  fof(f642,plain,(
% 1.61/0.60    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~spl2_28),
% 1.61/0.60    inference(avatar_component_clause,[],[f640])).
% 1.61/0.60  fof(f504,plain,(
% 1.61/0.60    m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) | ~spl2_26),
% 1.61/0.60    inference(avatar_component_clause,[],[f502])).
% 1.61/0.60  fof(f643,plain,(
% 1.61/0.60    spl2_28 | ~spl2_11 | ~spl2_12),
% 1.61/0.60    inference(avatar_split_clause,[],[f233,f216,f211,f640])).
% 1.61/0.60  fof(f216,plain,(
% 1.61/0.60    spl2_12 <=> v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.61/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 1.61/0.60  fof(f233,plain,(
% 1.61/0.60    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (~spl2_11 | ~spl2_12)),
% 1.61/0.60    inference(unit_resulting_resolution,[],[f213,f218,f45])).
% 1.61/0.60  fof(f45,plain,(
% 1.61/0.60    ( ! [X0] : (~v1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~l1_pre_topc(X0)) )),
% 1.61/0.60    inference(cnf_transformation,[],[f19])).
% 1.61/0.60  fof(f19,plain,(
% 1.61/0.60    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 1.61/0.60    inference(flattening,[],[f18])).
% 1.61/0.60  fof(f18,plain,(
% 1.61/0.60    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 1.61/0.60    inference(ennf_transformation,[],[f3])).
% 1.61/0.60  fof(f3,axiom,(
% 1.61/0.60    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 1.61/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 1.61/0.60  fof(f218,plain,(
% 1.61/0.60    v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_12),
% 1.61/0.60    inference(avatar_component_clause,[],[f216])).
% 1.61/0.60  fof(f505,plain,(
% 1.61/0.60    spl2_26 | ~spl2_11),
% 1.61/0.60    inference(avatar_split_clause,[],[f220,f211,f502])).
% 1.61/0.60  fof(f220,plain,(
% 1.61/0.60    m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) | ~spl2_11),
% 1.61/0.60    inference(unit_resulting_resolution,[],[f213,f44])).
% 1.61/0.60  fof(f44,plain,(
% 1.61/0.60    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.61/0.60    inference(cnf_transformation,[],[f17])).
% 1.61/0.60  fof(f17,plain,(
% 1.61/0.60    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.61/0.60    inference(ennf_transformation,[],[f7])).
% 1.61/0.60  fof(f7,axiom,(
% 1.61/0.60    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.61/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 1.61/0.60  fof(f239,plain,(
% 1.61/0.60    spl2_13 | ~spl2_1 | ~spl2_7),
% 1.61/0.60    inference(avatar_split_clause,[],[f129,f112,f62,f236])).
% 1.61/0.60  fof(f129,plain,(
% 1.61/0.60    m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl2_1 | ~spl2_7)),
% 1.61/0.60    inference(subsumption_resolution,[],[f128,f116])).
% 1.61/0.60  fof(f116,plain,(
% 1.61/0.60    l1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0))) | (~spl2_1 | ~spl2_7)),
% 1.61/0.60    inference(unit_resulting_resolution,[],[f64,f114,f48])).
% 1.61/0.60  fof(f48,plain,(
% 1.61/0.60    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.61/0.60    inference(cnf_transformation,[],[f21])).
% 1.61/0.60  fof(f21,plain,(
% 1.61/0.60    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.61/0.60    inference(ennf_transformation,[],[f6])).
% 1.61/0.60  fof(f6,axiom,(
% 1.61/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.61/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.61/0.60  fof(f128,plain,(
% 1.61/0.60    m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0))) | (~spl2_1 | ~spl2_7)),
% 1.61/0.60    inference(subsumption_resolution,[],[f119,f64])).
% 1.61/0.60  fof(f119,plain,(
% 1.61/0.60    m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(sK0) | ~l1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0))) | ~spl2_7),
% 1.61/0.60    inference(resolution,[],[f114,f46])).
% 1.61/0.60  fof(f46,plain,(
% 1.61/0.60    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.61/0.60    inference(cnf_transformation,[],[f34])).
% 1.61/0.60  fof(f34,plain,(
% 1.61/0.60    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.61/0.60    inference(nnf_transformation,[],[f20])).
% 1.61/0.60  fof(f20,plain,(
% 1.61/0.60    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.61/0.60    inference(ennf_transformation,[],[f10])).
% 1.61/0.60  fof(f10,axiom,(
% 1.61/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 1.61/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).
% 1.61/0.60  fof(f219,plain,(
% 1.61/0.60    spl2_12 | ~spl2_8),
% 1.61/0.60    inference(avatar_split_clause,[],[f136,f131,f216])).
% 1.61/0.60  fof(f131,plain,(
% 1.61/0.60    spl2_8 <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.61/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 1.61/0.60  fof(f136,plain,(
% 1.61/0.60    v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_8),
% 1.61/0.60    inference(unit_resulting_resolution,[],[f133,f52])).
% 1.61/0.60  fof(f52,plain,(
% 1.61/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | v1_pre_topc(g1_pre_topc(X0,X1))) )),
% 1.61/0.60    inference(cnf_transformation,[],[f25])).
% 1.61/0.60  fof(f25,plain,(
% 1.61/0.60    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.61/0.60    inference(ennf_transformation,[],[f4])).
% 1.61/0.60  fof(f4,axiom,(
% 1.61/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 1.61/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 1.61/0.60  fof(f133,plain,(
% 1.61/0.60    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl2_8),
% 1.61/0.60    inference(avatar_component_clause,[],[f131])).
% 1.61/0.60  fof(f214,plain,(
% 1.61/0.60    spl2_11 | ~spl2_8),
% 1.61/0.60    inference(avatar_split_clause,[],[f135,f131,f211])).
% 1.61/0.60  fof(f135,plain,(
% 1.61/0.60    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_8),
% 1.61/0.60    inference(unit_resulting_resolution,[],[f133,f53])).
% 1.61/0.60  fof(f53,plain,(
% 1.61/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | l1_pre_topc(g1_pre_topc(X0,X1))) )),
% 1.61/0.60    inference(cnf_transformation,[],[f25])).
% 1.61/0.60  fof(f153,plain,(
% 1.61/0.60    spl2_9 | ~spl2_1),
% 1.61/0.60    inference(avatar_split_clause,[],[f105,f62,f150])).
% 1.61/0.60  fof(f134,plain,(
% 1.61/0.60    spl2_8 | ~spl2_1),
% 1.61/0.60    inference(avatar_split_clause,[],[f88,f62,f131])).
% 1.61/0.60  fof(f88,plain,(
% 1.61/0.60    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl2_1),
% 1.61/0.60    inference(unit_resulting_resolution,[],[f64,f44])).
% 1.61/0.60  fof(f115,plain,(
% 1.61/0.60    spl2_7 | ~spl2_1),
% 1.61/0.60    inference(avatar_split_clause,[],[f98,f62,f112])).
% 1.61/0.60  fof(f98,plain,(
% 1.61/0.60    m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),sK0) | ~spl2_1),
% 1.61/0.60    inference(unit_resulting_resolution,[],[f64,f60,f57])).
% 1.61/0.60  fof(f57,plain,(
% 1.61/0.60    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(k1_pre_topc(X0,X1),X0)) )),
% 1.61/0.60    inference(cnf_transformation,[],[f28])).
% 1.61/0.60  fof(f28,plain,(
% 1.61/0.60    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.61/0.60    inference(flattening,[],[f27])).
% 1.61/0.60  fof(f27,plain,(
% 1.61/0.60    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.61/0.60    inference(ennf_transformation,[],[f5])).
% 1.61/0.60  fof(f5,axiom,(
% 1.61/0.60    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 1.61/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).
% 1.61/0.60  fof(f95,plain,(
% 1.61/0.60    spl2_4 | spl2_5),
% 1.61/0.60    inference(avatar_split_clause,[],[f40,f82,f77])).
% 1.61/0.60  fof(f77,plain,(
% 1.61/0.60    spl2_4 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.61/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.61/0.60  fof(f40,plain,(
% 1.61/0.60    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.61/0.60    inference(cnf_transformation,[],[f33])).
% 1.61/0.60  fof(f74,plain,(
% 1.61/0.60    spl2_2 | spl2_3),
% 1.61/0.60    inference(avatar_split_clause,[],[f37,f71,f67])).
% 1.61/0.60  fof(f37,plain,(
% 1.61/0.60    v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v2_compts_1(sK1,sK0)),
% 1.61/0.60    inference(cnf_transformation,[],[f33])).
% 1.61/0.60  fof(f65,plain,(
% 1.61/0.60    spl2_1),
% 1.61/0.60    inference(avatar_split_clause,[],[f36,f62])).
% 1.61/0.60  fof(f36,plain,(
% 1.61/0.60    l1_pre_topc(sK0)),
% 1.61/0.60    inference(cnf_transformation,[],[f33])).
% 1.61/0.60  % SZS output end Proof for theBenchmark
% 1.61/0.60  % (27046)------------------------------
% 1.61/0.60  % (27046)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.60  % (27046)Termination reason: Refutation
% 1.61/0.60  
% 1.61/0.60  % (27046)Memory used [KB]: 11257
% 1.61/0.60  % (27046)Time elapsed: 0.117 s
% 1.61/0.60  % (27046)------------------------------
% 1.61/0.60  % (27046)------------------------------
% 1.61/0.60  % (27022)Success in time 0.233 s
%------------------------------------------------------------------------------
