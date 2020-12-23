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
% DateTime   : Thu Dec  3 13:13:30 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 192 expanded)
%              Number of leaves         :   25 (  90 expanded)
%              Depth                    :    7
%              Number of atoms          :  260 ( 590 expanded)
%              Number of equality atoms :   24 (  38 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f642,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f52,f57,f62,f67,f74,f79,f102,f107,f205,f330,f468,f554,f616,f641])).

fof(f641,plain,
    ( ~ spl3_70
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f561,f64,f59,f54,f49,f44,f613])).

fof(f613,plain,
    ( spl3_70
  <=> r1_tarski(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).

fof(f44,plain,
    ( spl3_1
  <=> v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f49,plain,
    ( spl3_2
  <=> v1_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f54,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f59,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f64,plain,
    ( spl3_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f561,plain,
    ( ~ r1_tarski(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK1)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f66,f51,f61,f46,f86,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_2(X2,X0)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_2(X1,X0)
              | ~ v1_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_2(X1,X0)
              | ~ v1_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( ( v1_tops_2(X2,X0)
                  & r1_tarski(X1,X2) )
               => v1_tops_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_tops_2)).

fof(f86,plain,
    ( ! [X0] : m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f56,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f56,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f46,plain,
    ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f61,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f51,plain,
    ( v1_tops_2(sK1,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f66,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f616,plain,
    ( spl3_70
    | ~ spl3_3
    | ~ spl3_68 ),
    inference(avatar_split_clause,[],[f609,f551,f54,f613])).

fof(f551,plain,
    ( spl3_68
  <=> r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).

fof(f609,plain,
    ( r1_tarski(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK1)
    | ~ spl3_3
    | ~ spl3_68 ),
    inference(backward_demodulation,[],[f553,f604])).

fof(f604,plain,
    ( ! [X0] : k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2)))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f86,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f553,plain,
    ( r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))),sK1)
    | ~ spl3_68 ),
    inference(avatar_component_clause,[],[f551])).

fof(f554,plain,
    ( spl3_68
    | ~ spl3_19
    | ~ spl3_56 ),
    inference(avatar_split_clause,[],[f548,f465,f202,f551])).

fof(f202,plain,
    ( spl3_19
  <=> r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f465,plain,
    ( spl3_56
  <=> k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2)) = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f548,plain,
    ( r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))),sK1)
    | ~ spl3_19
    | ~ spl3_56 ),
    inference(backward_demodulation,[],[f204,f467])).

fof(f467,plain,
    ( k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2)) = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))
    | ~ spl3_56 ),
    inference(avatar_component_clause,[],[f465])).

% (5980)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% (5965)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% (5971)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
fof(f204,plain,
    ( r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2))),sK1)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f202])).

fof(f468,plain,
    ( spl3_56
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f463,f327,f76,f59,f465])).

fof(f76,plain,
    ( spl3_7
  <=> m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f327,plain,
    ( spl3_36
  <=> k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) = k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f463,plain,
    ( k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2)) = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_36 ),
    inference(forward_demodulation,[],[f443,f329])).

fof(f329,plain,
    ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) = k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2))
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f327])).

fof(f443,plain,
    ( k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2)) = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2)))
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f61,f78,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_subset_1)).

fof(f78,plain,
    ( m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f76])).

fof(f330,plain,
    ( spl3_36
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f325,f104,f76,f59,f327])).

fof(f104,plain,
    ( spl3_11
  <=> sK2 = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f325,plain,
    ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) = k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2))
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f302,f106])).

fof(f106,plain,
    ( sK2 = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f104])).

fof(f302,plain,
    ( k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2)))
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f61,f78,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

fof(f205,plain,
    ( spl3_19
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f200,f99,f76,f71,f202])).

fof(f71,plain,
    ( spl3_6
  <=> m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f99,plain,
    ( spl3_10
  <=> sK1 = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f200,plain,
    ( r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2))),sK1)
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f187,f101])).

fof(f101,plain,
    ( sK1 = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f99])).

fof(f187,plain,
    ( r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2))),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)))
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f73,f78,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).

fof(f73,plain,
    ( m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f71])).

fof(f107,plain,
    ( spl3_11
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f89,f54,f104])).

fof(f89,plain,
    ( sK2 = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f56,f41])).

fof(f102,plain,
    ( spl3_10
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f90,f59,f99])).

fof(f90,plain,
    ( sK1 = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f61,f41])).

fof(f79,plain,
    ( spl3_7
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f68,f54,f76])).

fof(f68,plain,
    ( m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f56,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f74,plain,
    ( spl3_6
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f69,f59,f71])).

fof(f69,plain,
    ( m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f61,f42])).

fof(f67,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f29,f64])).

fof(f29,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    & v1_tops_2(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f27,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
                & v1_tops_2(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0)
              & v1_tops_2(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0)
            & v1_tops_2(X1,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ? [X2] :
          ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0)
          & v1_tops_2(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X2] :
        ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0)
        & v1_tops_2(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
      & v1_tops_2(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( v1_tops_2(X1,X0)
                 => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( v1_tops_2(X1,X0)
               => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_tops_2)).

fof(f62,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f30,f59])).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f28])).

fof(f57,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f31,f54])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f28])).

fof(f52,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f32,f49])).

fof(f32,plain,(
    v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f47,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f33,f44])).

fof(f33,plain,(
    ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:56:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.51  % (5979)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.51  % (5972)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.51  % (5963)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.52  % (5967)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.52  % (5966)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.52  % (5968)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.53  % (5969)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.53  % (5984)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.53  % (5986)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.53  % (5985)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.53  % (5982)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.53  % (5975)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.54  % (5978)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.54  % (5966)Refutation not found, incomplete strategy% (5966)------------------------------
% 0.20/0.54  % (5966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (5966)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (5966)Memory used [KB]: 10618
% 0.20/0.54  % (5966)Time elapsed: 0.094 s
% 0.20/0.54  % (5966)------------------------------
% 0.20/0.54  % (5966)------------------------------
% 0.20/0.54  % (5986)Refutation not found, incomplete strategy% (5986)------------------------------
% 0.20/0.54  % (5986)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (5986)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (5986)Memory used [KB]: 10618
% 0.20/0.54  % (5986)Time elapsed: 0.063 s
% 0.20/0.54  % (5986)------------------------------
% 0.20/0.54  % (5986)------------------------------
% 0.20/0.54  % (5977)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.54  % (5964)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.54  % (5974)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.54  % (5976)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.55  % (5970)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.55  % (5973)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.55  % (5983)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.56  % (5969)Refutation found. Thanks to Tanya!
% 0.20/0.56  % SZS status Theorem for theBenchmark
% 0.20/0.56  % SZS output start Proof for theBenchmark
% 0.20/0.56  fof(f642,plain,(
% 0.20/0.56    $false),
% 0.20/0.56    inference(avatar_sat_refutation,[],[f47,f52,f57,f62,f67,f74,f79,f102,f107,f205,f330,f468,f554,f616,f641])).
% 0.20/0.56  fof(f641,plain,(
% 0.20/0.56    ~spl3_70 | spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5),
% 0.20/0.56    inference(avatar_split_clause,[],[f561,f64,f59,f54,f49,f44,f613])).
% 0.20/0.56  fof(f613,plain,(
% 0.20/0.56    spl3_70 <=> r1_tarski(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK1)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).
% 0.20/0.56  fof(f44,plain,(
% 0.20/0.56    spl3_1 <=> v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.56  fof(f49,plain,(
% 0.20/0.56    spl3_2 <=> v1_tops_2(sK1,sK0)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.56  fof(f54,plain,(
% 0.20/0.56    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.56  fof(f59,plain,(
% 0.20/0.56    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.56  fof(f64,plain,(
% 0.20/0.56    spl3_5 <=> l1_pre_topc(sK0)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.56  fof(f561,plain,(
% 0.20/0.56    ~r1_tarski(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK1) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5)),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f66,f51,f61,f46,f86,f37])).
% 0.20/0.56  fof(f37,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_2(X1,X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f18])).
% 0.20/0.56  fof(f18,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (! [X2] : (v1_tops_2(X1,X0) | ~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.56    inference(flattening,[],[f17])).
% 0.20/0.56  fof(f17,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (! [X2] : ((v1_tops_2(X1,X0) | (~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f9])).
% 0.20/0.56  fof(f9,axiom,(
% 0.20/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_tops_2(X2,X0) & r1_tarski(X1,X2)) => v1_tops_2(X1,X0)))))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_tops_2)).
% 0.20/0.56  fof(f86,plain,(
% 0.20/0.56    ( ! [X0] : (m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl3_3),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f56,f35])).
% 0.20/0.56  fof(f35,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f15])).
% 0.20/0.56  fof(f15,plain,(
% 0.20/0.56    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f4])).
% 0.20/0.56  fof(f4,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 0.20/0.56  fof(f56,plain,(
% 0.20/0.56    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_3),
% 0.20/0.56    inference(avatar_component_clause,[],[f54])).
% 0.20/0.56  fof(f46,plain,(
% 0.20/0.56    ~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) | spl3_1),
% 0.20/0.56    inference(avatar_component_clause,[],[f44])).
% 0.20/0.56  fof(f61,plain,(
% 0.20/0.56    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_4),
% 0.20/0.56    inference(avatar_component_clause,[],[f59])).
% 0.20/0.56  fof(f51,plain,(
% 0.20/0.56    v1_tops_2(sK1,sK0) | ~spl3_2),
% 0.20/0.56    inference(avatar_component_clause,[],[f49])).
% 0.20/0.56  fof(f66,plain,(
% 0.20/0.56    l1_pre_topc(sK0) | ~spl3_5),
% 0.20/0.56    inference(avatar_component_clause,[],[f64])).
% 0.20/0.56  fof(f616,plain,(
% 0.20/0.56    spl3_70 | ~spl3_3 | ~spl3_68),
% 0.20/0.56    inference(avatar_split_clause,[],[f609,f551,f54,f613])).
% 0.20/0.56  fof(f551,plain,(
% 0.20/0.56    spl3_68 <=> r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))),sK1)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).
% 0.20/0.56  fof(f609,plain,(
% 0.20/0.56    r1_tarski(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK1) | (~spl3_3 | ~spl3_68)),
% 0.20/0.56    inference(backward_demodulation,[],[f553,f604])).
% 0.20/0.56  fof(f604,plain,(
% 0.20/0.56    ( ! [X0] : (k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2)))) ) | ~spl3_3),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f86,f41])).
% 0.20/0.56  fof(f41,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f23])).
% 0.20/0.56  fof(f23,plain,(
% 0.20/0.56    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f5])).
% 0.20/0.56  fof(f5,axiom,(
% 0.20/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.20/0.56  fof(f553,plain,(
% 0.20/0.56    r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))),sK1) | ~spl3_68),
% 0.20/0.56    inference(avatar_component_clause,[],[f551])).
% 0.20/0.56  fof(f554,plain,(
% 0.20/0.56    spl3_68 | ~spl3_19 | ~spl3_56),
% 0.20/0.56    inference(avatar_split_clause,[],[f548,f465,f202,f551])).
% 0.20/0.56  fof(f202,plain,(
% 0.20/0.56    spl3_19 <=> r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2))),sK1)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.20/0.56  fof(f465,plain,(
% 0.20/0.56    spl3_56 <=> k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2)) = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 0.20/0.56  fof(f548,plain,(
% 0.20/0.56    r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))),sK1) | (~spl3_19 | ~spl3_56)),
% 0.20/0.56    inference(backward_demodulation,[],[f204,f467])).
% 0.20/0.56  fof(f467,plain,(
% 0.20/0.56    k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2)) = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)) | ~spl3_56),
% 0.20/0.56    inference(avatar_component_clause,[],[f465])).
% 0.20/0.56  % (5980)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.56  % (5965)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.57  % (5971)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.57  fof(f204,plain,(
% 0.20/0.57    r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2))),sK1) | ~spl3_19),
% 0.20/0.57    inference(avatar_component_clause,[],[f202])).
% 0.20/0.57  fof(f468,plain,(
% 0.20/0.57    spl3_56 | ~spl3_4 | ~spl3_7 | ~spl3_36),
% 0.20/0.57    inference(avatar_split_clause,[],[f463,f327,f76,f59,f465])).
% 0.20/0.57  fof(f76,plain,(
% 0.20/0.57    spl3_7 <=> m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.57  fof(f327,plain,(
% 0.20/0.57    spl3_36 <=> k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) = k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.20/0.57  fof(f463,plain,(
% 0.20/0.57    k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2)) = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)) | (~spl3_4 | ~spl3_7 | ~spl3_36)),
% 0.20/0.57    inference(forward_demodulation,[],[f443,f329])).
% 0.20/0.57  fof(f329,plain,(
% 0.20/0.57    k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) = k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2)) | ~spl3_36),
% 0.20/0.57    inference(avatar_component_clause,[],[f327])).
% 0.20/0.57  fof(f443,plain,(
% 0.20/0.57    k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2)) = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2))) | (~spl3_4 | ~spl3_7)),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f61,f78,f39])).
% 0.20/0.57  fof(f39,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f21])).
% 0.20/0.57  fof(f21,plain,(
% 0.20/0.57    ! [X0,X1] : (! [X2] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f7])).
% 0.20/0.57  fof(f7,axiom,(
% 0.20/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_subset_1)).
% 0.20/0.57  fof(f78,plain,(
% 0.20/0.57    m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_7),
% 0.20/0.57    inference(avatar_component_clause,[],[f76])).
% 0.20/0.57  fof(f330,plain,(
% 0.20/0.57    spl3_36 | ~spl3_4 | ~spl3_7 | ~spl3_11),
% 0.20/0.57    inference(avatar_split_clause,[],[f325,f104,f76,f59,f327])).
% 0.20/0.57  fof(f104,plain,(
% 0.20/0.57    spl3_11 <=> sK2 = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.57  fof(f325,plain,(
% 0.20/0.57    k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) = k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2)) | (~spl3_4 | ~spl3_7 | ~spl3_11)),
% 0.20/0.57    inference(forward_demodulation,[],[f302,f106])).
% 0.20/0.57  fof(f106,plain,(
% 0.20/0.57    sK2 = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2)) | ~spl3_11),
% 0.20/0.57    inference(avatar_component_clause,[],[f104])).
% 0.20/0.57  fof(f302,plain,(
% 0.20/0.57    k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2))) | (~spl3_4 | ~spl3_7)),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f61,f78,f36])).
% 0.20/0.57  fof(f36,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f16])).
% 0.20/0.57  fof(f16,plain,(
% 0.20/0.57    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f6])).
% 0.20/0.57  fof(f6,axiom,(
% 0.20/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).
% 0.20/0.57  fof(f205,plain,(
% 0.20/0.57    spl3_19 | ~spl3_6 | ~spl3_7 | ~spl3_10),
% 0.20/0.57    inference(avatar_split_clause,[],[f200,f99,f76,f71,f202])).
% 0.20/0.57  fof(f71,plain,(
% 0.20/0.57    spl3_6 <=> m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.57  fof(f99,plain,(
% 0.20/0.57    spl3_10 <=> sK1 = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.57  fof(f200,plain,(
% 0.20/0.57    r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2))),sK1) | (~spl3_6 | ~spl3_7 | ~spl3_10)),
% 0.20/0.57    inference(forward_demodulation,[],[f187,f101])).
% 0.20/0.57  fof(f101,plain,(
% 0.20/0.57    sK1 = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)) | ~spl3_10),
% 0.20/0.57    inference(avatar_component_clause,[],[f99])).
% 0.20/0.57  fof(f187,plain,(
% 0.20/0.57    r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2))),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1))) | (~spl3_6 | ~spl3_7)),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f73,f78,f40])).
% 0.20/0.57  fof(f40,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f22])).
% 0.20/0.57  fof(f22,plain,(
% 0.20/0.57    ! [X0,X1] : (! [X2] : (r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f8])).
% 0.20/0.57  fof(f8,axiom,(
% 0.20/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).
% 0.20/0.57  fof(f73,plain,(
% 0.20/0.57    m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_6),
% 0.20/0.57    inference(avatar_component_clause,[],[f71])).
% 0.20/0.57  fof(f107,plain,(
% 0.20/0.57    spl3_11 | ~spl3_3),
% 0.20/0.57    inference(avatar_split_clause,[],[f89,f54,f104])).
% 0.20/0.57  fof(f89,plain,(
% 0.20/0.57    sK2 = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2)) | ~spl3_3),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f56,f41])).
% 0.20/0.57  fof(f102,plain,(
% 0.20/0.57    spl3_10 | ~spl3_4),
% 0.20/0.57    inference(avatar_split_clause,[],[f90,f59,f99])).
% 0.20/0.57  fof(f90,plain,(
% 0.20/0.57    sK1 = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)) | ~spl3_4),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f61,f41])).
% 0.20/0.57  fof(f79,plain,(
% 0.20/0.57    spl3_7 | ~spl3_3),
% 0.20/0.57    inference(avatar_split_clause,[],[f68,f54,f76])).
% 0.20/0.57  fof(f68,plain,(
% 0.20/0.57    m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_3),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f56,f42])).
% 0.20/0.57  fof(f42,plain,(
% 0.20/0.57    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f24])).
% 0.20/0.57  fof(f24,plain,(
% 0.20/0.57    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f3])).
% 0.20/0.57  fof(f3,axiom,(
% 0.20/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.20/0.57  fof(f74,plain,(
% 0.20/0.57    spl3_6 | ~spl3_4),
% 0.20/0.57    inference(avatar_split_clause,[],[f69,f59,f71])).
% 0.20/0.57  fof(f69,plain,(
% 0.20/0.57    m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_4),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f61,f42])).
% 0.20/0.57  fof(f67,plain,(
% 0.20/0.57    spl3_5),
% 0.20/0.57    inference(avatar_split_clause,[],[f29,f64])).
% 0.20/0.57  fof(f29,plain,(
% 0.20/0.57    l1_pre_topc(sK0)),
% 0.20/0.57    inference(cnf_transformation,[],[f28])).
% 0.20/0.57  fof(f28,plain,(
% 0.20/0.57    ((~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) & v1_tops_2(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0)),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f27,f26,f25])).
% 0.20/0.57  fof(f25,plain,(
% 0.20/0.57    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0) & v1_tops_2(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f26,plain,(
% 0.20/0.57    ? [X1] : (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0) & v1_tops_2(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0) & v1_tops_2(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f27,plain,(
% 0.20/0.57    ? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0) & v1_tops_2(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) & v1_tops_2(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f13,plain,(
% 0.20/0.57    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.20/0.57    inference(flattening,[],[f12])).
% 0.20/0.57  fof(f12,plain,(
% 0.20/0.57    ? [X0] : (? [X1] : (? [X2] : ((~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.20/0.57    inference(ennf_transformation,[],[f11])).
% 0.20/0.57  fof(f11,negated_conjecture,(
% 0.20/0.57    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 0.20/0.57    inference(negated_conjecture,[],[f10])).
% 0.20/0.57  fof(f10,conjecture,(
% 0.20/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_tops_2)).
% 0.20/0.57  fof(f62,plain,(
% 0.20/0.57    spl3_4),
% 0.20/0.57    inference(avatar_split_clause,[],[f30,f59])).
% 0.20/0.57  fof(f30,plain,(
% 0.20/0.57    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.57    inference(cnf_transformation,[],[f28])).
% 0.20/0.57  fof(f57,plain,(
% 0.20/0.57    spl3_3),
% 0.20/0.57    inference(avatar_split_clause,[],[f31,f54])).
% 0.20/0.57  fof(f31,plain,(
% 0.20/0.57    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.57    inference(cnf_transformation,[],[f28])).
% 0.20/0.57  fof(f52,plain,(
% 0.20/0.57    spl3_2),
% 0.20/0.57    inference(avatar_split_clause,[],[f32,f49])).
% 0.20/0.57  fof(f32,plain,(
% 0.20/0.57    v1_tops_2(sK1,sK0)),
% 0.20/0.57    inference(cnf_transformation,[],[f28])).
% 0.20/0.57  fof(f47,plain,(
% 0.20/0.57    ~spl3_1),
% 0.20/0.57    inference(avatar_split_clause,[],[f33,f44])).
% 0.20/0.57  fof(f33,plain,(
% 0.20/0.57    ~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 0.20/0.57    inference(cnf_transformation,[],[f28])).
% 0.20/0.57  % SZS output end Proof for theBenchmark
% 0.20/0.57  % (5969)------------------------------
% 0.20/0.57  % (5969)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (5969)Termination reason: Refutation
% 0.20/0.57  
% 0.20/0.57  % (5969)Memory used [KB]: 11257
% 0.20/0.57  % (5969)Time elapsed: 0.139 s
% 0.20/0.57  % (5969)------------------------------
% 0.20/0.57  % (5969)------------------------------
% 0.20/0.58  % (5962)Success in time 0.218 s
%------------------------------------------------------------------------------
