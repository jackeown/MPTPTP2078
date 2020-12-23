%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1476+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:57 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  192 ( 367 expanded)
%              Number of leaves         :   45 ( 174 expanded)
%              Depth                    :    8
%              Number of atoms          :  535 ( 968 expanded)
%              Number of equality atoms :   83 ( 158 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f659,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f84,f89,f98,f99,f113,f118,f124,f130,f151,f194,f218,f234,f296,f300,f306,f319,f326,f331,f351,f363,f389,f401,f444,f459,f479,f562,f567,f589,f598,f630,f632,f639,f649,f656])).

fof(f656,plain,
    ( ~ spl5_4
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_2
    | spl5_69 ),
    inference(avatar_split_clause,[],[f652,f586,f81,f86,f76,f91])).

fof(f91,plain,
    ( spl5_4
  <=> r1_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f76,plain,
    ( spl5_1
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f86,plain,
    ( spl5_3
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f81,plain,
    ( spl5_2
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f586,plain,
    ( spl5_69
  <=> r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_69])])).

fof(f652,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ r1_orders_2(sK0,sK1,sK2)
    | spl5_69 ),
    inference(resolution,[],[f588,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

% (23119)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

fof(f588,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | spl5_69 ),
    inference(avatar_component_clause,[],[f586])).

fof(f649,plain,
    ( ~ spl5_65
    | ~ spl5_66
    | ~ spl5_69
    | ~ spl5_57
    | spl5_70 ),
    inference(avatar_split_clause,[],[f648,f595,f476,f586,f547,f543])).

fof(f543,plain,
    ( spl5_65
  <=> v1_relat_1(u1_orders_2(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).

fof(f547,plain,
    ( spl5_66
  <=> v1_relat_1(u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_66])])).

fof(f476,plain,
    ( spl5_57
  <=> u1_orders_2(sK0) = k4_relat_1(u1_orders_2(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).

fof(f595,plain,
    ( spl5_70
  <=> r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).

fof(f648,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ v1_relat_1(u1_orders_2(k7_lattice3(sK0)))
    | ~ spl5_57
    | spl5_70 ),
    inference(forward_demodulation,[],[f647,f478])).

fof(f478,plain,
    ( u1_orders_2(sK0) = k4_relat_1(u1_orders_2(k7_lattice3(sK0)))
    | ~ spl5_57 ),
    inference(avatar_component_clause,[],[f476])).

fof(f647,plain,
    ( ~ v1_relat_1(u1_orders_2(sK0))
    | ~ v1_relat_1(u1_orders_2(k7_lattice3(sK0)))
    | ~ r2_hidden(k4_tarski(sK1,sK2),k4_relat_1(u1_orders_2(k7_lattice3(sK0))))
    | ~ spl5_57
    | spl5_70 ),
    inference(forward_demodulation,[],[f645,f478])).

fof(f645,plain,
    ( ~ v1_relat_1(k4_relat_1(u1_orders_2(k7_lattice3(sK0))))
    | ~ v1_relat_1(u1_orders_2(k7_lattice3(sK0)))
    | ~ r2_hidden(k4_tarski(sK1,sK2),k4_relat_1(u1_orders_2(k7_lattice3(sK0))))
    | spl5_70 ),
    inference(resolution,[],[f597,f73])).

fof(f73,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(k4_tarski(X3,X2),X0)
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X2,X3),k4_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | r2_hidden(k4_tarski(X3,X2),X0)
      | ~ r2_hidden(k4_tarski(X2,X3),X1)
      | k4_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_1)).

fof(f597,plain,
    ( ~ r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(k7_lattice3(sK0)))
    | spl5_70 ),
    inference(avatar_component_clause,[],[f595])).

fof(f639,plain,
    ( ~ spl5_17
    | ~ spl5_70
    | ~ spl5_3
    | ~ spl5_2
    | spl5_9
    | ~ spl5_41 ),
    inference(avatar_split_clause,[],[f638,f360,f127,f81,f86,f595,f183])).

fof(f183,plain,
    ( spl5_17
  <=> l1_orders_2(k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f127,plain,
    ( spl5_9
  <=> r1_orders_2(k7_lattice3(sK0),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

% (23126)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f360,plain,
    ( spl5_41
  <=> u1_struct_0(sK0) = u1_struct_0(k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f638,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(k7_lattice3(sK0)))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | spl5_9
    | ~ spl5_41 ),
    inference(forward_demodulation,[],[f637,f362])).

fof(f362,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k7_lattice3(sK0))
    | ~ spl5_41 ),
    inference(avatar_component_clause,[],[f360])).

fof(f637,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(k7_lattice3(sK0)))
    | ~ r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(k7_lattice3(sK0)))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | spl5_9
    | ~ spl5_41 ),
    inference(forward_demodulation,[],[f636,f362])).

fof(f636,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(k7_lattice3(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k7_lattice3(sK0)))
    | ~ r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(k7_lattice3(sK0)))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | spl5_9 ),
    inference(resolution,[],[f128,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f128,plain,
    ( ~ r1_orders_2(k7_lattice3(sK0),sK2,sK1)
    | spl5_9 ),
    inference(avatar_component_clause,[],[f127])).

fof(f632,plain,
    ( sK1 != k8_lattice3(sK0,sK1)
    | sK2 != k8_lattice3(sK0,sK2)
    | r1_orders_2(k7_lattice3(sK0),k8_lattice3(sK0,sK2),k8_lattice3(sK0,sK1))
    | ~ r1_orders_2(k7_lattice3(sK0),sK2,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f630,plain,
    ( ~ spl5_9
    | ~ spl5_17
    | ~ spl5_3
    | ~ spl5_2
    | ~ spl5_41
    | spl5_70 ),
    inference(avatar_split_clause,[],[f629,f595,f360,f81,f86,f183,f127])).

fof(f629,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ r1_orders_2(k7_lattice3(sK0),sK2,sK1)
    | ~ spl5_41
    | spl5_70 ),
    inference(forward_demodulation,[],[f628,f362])).

fof(f628,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(k7_lattice3(sK0)))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ r1_orders_2(k7_lattice3(sK0),sK2,sK1)
    | ~ spl5_41
    | spl5_70 ),
    inference(forward_demodulation,[],[f626,f362])).

fof(f626,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(k7_lattice3(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k7_lattice3(sK0)))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ r1_orders_2(k7_lattice3(sK0),sK2,sK1)
    | spl5_70 ),
    inference(resolution,[],[f60,f597])).

fof(f598,plain,
    ( ~ spl5_66
    | ~ spl5_65
    | ~ spl5_70
    | ~ spl5_54
    | spl5_69 ),
    inference(avatar_split_clause,[],[f593,f586,f456,f595,f543,f547])).

fof(f456,plain,
    ( spl5_54
  <=> k4_relat_1(u1_orders_2(sK0)) = u1_orders_2(k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f593,plain,
    ( ~ r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(k7_lattice3(sK0)))
    | ~ v1_relat_1(u1_orders_2(k7_lattice3(sK0)))
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl5_54
    | spl5_69 ),
    inference(forward_demodulation,[],[f592,f458])).

fof(f458,plain,
    ( k4_relat_1(u1_orders_2(sK0)) = u1_orders_2(k7_lattice3(sK0))
    | ~ spl5_54 ),
    inference(avatar_component_clause,[],[f456])).

fof(f592,plain,
    ( ~ v1_relat_1(u1_orders_2(k7_lattice3(sK0)))
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ r2_hidden(k4_tarski(sK2,sK1),k4_relat_1(u1_orders_2(sK0)))
    | ~ spl5_54
    | spl5_69 ),
    inference(forward_demodulation,[],[f590,f458])).

fof(f590,plain,
    ( ~ v1_relat_1(k4_relat_1(u1_orders_2(sK0)))
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ r2_hidden(k4_tarski(sK2,sK1),k4_relat_1(u1_orders_2(sK0)))
    | spl5_69 ),
    inference(resolution,[],[f588,f73])).

% (23112)Refutation not found, incomplete strategy% (23112)------------------------------
% (23112)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23112)Termination reason: Refutation not found, incomplete strategy

% (23112)Memory used [KB]: 10746
% (23112)Time elapsed: 0.103 s
% (23112)------------------------------
% (23112)------------------------------
% (23115)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% (23135)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% (23114)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% (23125)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
fof(f589,plain,
    ( ~ spl5_1
    | ~ spl5_69
    | ~ spl5_3
    | ~ spl5_2
    | spl5_4 ),
    inference(avatar_split_clause,[],[f584,f91,f81,f86,f586,f76])).

fof(f584,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ l1_orders_2(sK0)
    | spl5_4 ),
    inference(resolution,[],[f59,f93])).

fof(f93,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f91])).

fof(f567,plain,
    ( ~ spl5_33
    | spl5_66 ),
    inference(avatar_contradiction_clause,[],[f566])).

fof(f566,plain,
    ( $false
    | ~ spl5_33
    | spl5_66 ),
    inference(subsumption_resolution,[],[f294,f564])).

fof(f564,plain,
    ( ! [X0,X1] : ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl5_66 ),
    inference(resolution,[],[f549,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f549,plain,
    ( ~ v1_relat_1(u1_orders_2(sK0))
    | spl5_66 ),
    inference(avatar_component_clause,[],[f547])).

fof(f294,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f293])).

fof(f293,plain,
    ( spl5_33
  <=> m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f562,plain,
    ( ~ spl5_46
    | spl5_65 ),
    inference(avatar_contradiction_clause,[],[f561])).

fof(f561,plain,
    ( $false
    | ~ spl5_46
    | spl5_65 ),
    inference(subsumption_resolution,[],[f392,f559])).

fof(f559,plain,
    ( ! [X0,X1] : ~ m1_subset_1(u1_orders_2(k7_lattice3(sK0)),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl5_65 ),
    inference(resolution,[],[f545,f69])).

fof(f545,plain,
    ( ~ v1_relat_1(u1_orders_2(k7_lattice3(sK0)))
    | spl5_65 ),
    inference(avatar_component_clause,[],[f543])).

fof(f392,plain,
    ( m1_subset_1(u1_orders_2(k7_lattice3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl5_46 ),
    inference(avatar_component_clause,[],[f391])).

fof(f391,plain,
    ( spl5_46
  <=> m1_subset_1(u1_orders_2(k7_lattice3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f479,plain,
    ( spl5_57
    | ~ spl5_12
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f464,f456,f148,f476])).

fof(f148,plain,
    ( spl5_12
  <=> u1_orders_2(sK0) = k4_relat_1(k4_relat_1(u1_orders_2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f464,plain,
    ( u1_orders_2(sK0) = k4_relat_1(u1_orders_2(k7_lattice3(sK0)))
    | ~ spl5_12
    | ~ spl5_54 ),
    inference(backward_demodulation,[],[f150,f458])).

fof(f150,plain,
    ( u1_orders_2(sK0) = k4_relat_1(k4_relat_1(u1_orders_2(sK0)))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f148])).

fof(f459,plain,
    ( spl5_54
    | ~ spl5_45
    | ~ spl5_52 ),
    inference(avatar_split_clause,[],[f454,f442,f386,f456])).

fof(f386,plain,
    ( spl5_45
  <=> k7_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f442,plain,
    ( spl5_52
  <=> ! [X1,X0] :
        ( g1_orders_2(X0,X1) != k7_lattice3(sK0)
        | k4_relat_1(u1_orders_2(sK0)) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f454,plain,
    ( k4_relat_1(u1_orders_2(sK0)) = u1_orders_2(k7_lattice3(sK0))
    | ~ spl5_45
    | ~ spl5_52 ),
    inference(trivial_inequality_removal,[],[f453])).

fof(f453,plain,
    ( k7_lattice3(sK0) != k7_lattice3(sK0)
    | k4_relat_1(u1_orders_2(sK0)) = u1_orders_2(k7_lattice3(sK0))
    | ~ spl5_45
    | ~ spl5_52 ),
    inference(superposition,[],[f443,f388])).

fof(f388,plain,
    ( k7_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(k7_lattice3(sK0)))
    | ~ spl5_45 ),
    inference(avatar_component_clause,[],[f386])).

fof(f443,plain,
    ( ! [X0,X1] :
        ( g1_orders_2(X0,X1) != k7_lattice3(sK0)
        | k4_relat_1(u1_orders_2(sK0)) = X1 )
    | ~ spl5_52 ),
    inference(avatar_component_clause,[],[f442])).

fof(f444,plain,
    ( ~ spl5_37
    | spl5_52
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f436,f328,f442,f323])).

fof(f323,plain,
    ( spl5_37
  <=> m1_subset_1(k4_relat_1(u1_orders_2(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f328,plain,
    ( spl5_38
  <=> k7_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),k4_relat_1(u1_orders_2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f436,plain,
    ( ! [X0,X1] :
        ( g1_orders_2(X0,X1) != k7_lattice3(sK0)
        | ~ m1_subset_1(k4_relat_1(u1_orders_2(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | k4_relat_1(u1_orders_2(sK0)) = X1 )
    | ~ spl5_38 ),
    inference(superposition,[],[f66,f330])).

fof(f330,plain,
    ( k7_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),k4_relat_1(u1_orders_2(sK0)))
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f328])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(f401,plain,
    ( ~ spl5_17
    | spl5_46
    | ~ spl5_41 ),
    inference(avatar_split_clause,[],[f396,f360,f391,f183])).

fof(f396,plain,
    ( m1_subset_1(u1_orders_2(k7_lattice3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ spl5_41 ),
    inference(superposition,[],[f53,f362])).

fof(f53,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

% (23117)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
fof(f24,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f389,plain,
    ( spl5_45
    | ~ spl5_34
    | ~ spl5_41 ),
    inference(avatar_split_clause,[],[f377,f360,f303,f386])).

fof(f303,plain,
    ( spl5_34
  <=> k7_lattice3(sK0) = g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f377,plain,
    ( k7_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(k7_lattice3(sK0)))
    | ~ spl5_34
    | ~ spl5_41 ),
    inference(backward_demodulation,[],[f305,f362])).

fof(f305,plain,
    ( k7_lattice3(sK0) = g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0)))
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f303])).

fof(f363,plain,
    ( spl5_41
    | ~ spl5_34
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f358,f349,f303,f360])).

fof(f349,plain,
    ( spl5_40
  <=> ! [X1,X0] :
        ( g1_orders_2(X0,X1) != k7_lattice3(sK0)
        | u1_struct_0(sK0) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f358,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k7_lattice3(sK0))
    | ~ spl5_34
    | ~ spl5_40 ),
    inference(trivial_inequality_removal,[],[f353])).

fof(f353,plain,
    ( k7_lattice3(sK0) != k7_lattice3(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k7_lattice3(sK0))
    | ~ spl5_34
    | ~ spl5_40 ),
    inference(superposition,[],[f350,f305])).

fof(f350,plain,
    ( ! [X0,X1] :
        ( g1_orders_2(X0,X1) != k7_lattice3(sK0)
        | u1_struct_0(sK0) = X0 )
    | ~ spl5_40 ),
    inference(avatar_component_clause,[],[f349])).

fof(f351,plain,
    ( ~ spl5_37
    | spl5_40
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f345,f328,f349,f323])).

fof(f345,plain,
    ( ! [X0,X1] :
        ( g1_orders_2(X0,X1) != k7_lattice3(sK0)
        | ~ m1_subset_1(k4_relat_1(u1_orders_2(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | u1_struct_0(sK0) = X0 )
    | ~ spl5_38 ),
    inference(superposition,[],[f65,f330])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f331,plain,
    ( spl5_38
    | ~ spl5_21
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f321,f316,f215,f328])).

fof(f215,plain,
    ( spl5_21
  <=> k7_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f316,plain,
    ( spl5_36
  <=> k4_relat_1(u1_orders_2(sK0)) = k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f321,plain,
    ( k7_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),k4_relat_1(u1_orders_2(sK0)))
    | ~ spl5_21
    | ~ spl5_36 ),
    inference(backward_demodulation,[],[f217,f318])).

fof(f318,plain,
    ( k4_relat_1(u1_orders_2(sK0)) = k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0))
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f316])).

fof(f217,plain,
    ( k7_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f215])).

fof(f326,plain,
    ( spl5_37
    | ~ spl5_23
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f320,f316,f227,f323])).

fof(f227,plain,
    ( spl5_23
  <=> m1_subset_1(k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f320,plain,
    ( m1_subset_1(k4_relat_1(u1_orders_2(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl5_23
    | ~ spl5_36 ),
    inference(backward_demodulation,[],[f228,f318])).

fof(f228,plain,
    ( m1_subset_1(k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f227])).

fof(f319,plain,
    ( spl5_36
    | ~ spl5_33 ),
    inference(avatar_split_clause,[],[f308,f293,f316])).

fof(f308,plain,
    ( k4_relat_1(u1_orders_2(sK0)) = k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0))
    | ~ spl5_33 ),
    inference(resolution,[],[f294,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

fof(f306,plain,
    ( spl5_34
    | ~ spl5_17
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f301,f231,f183,f303])).

fof(f231,plain,
    ( spl5_24
  <=> v1_orders_2(k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f301,plain,
    ( ~ l1_orders_2(k7_lattice3(sK0))
    | k7_lattice3(sK0) = g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0)))
    | ~ spl5_24 ),
    inference(resolution,[],[f233,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

fof(f233,plain,
    ( v1_orders_2(k7_lattice3(sK0))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f231])).

fof(f300,plain,
    ( ~ spl5_1
    | spl5_33 ),
    inference(avatar_split_clause,[],[f298,f293,f76])).

fof(f298,plain,
    ( ~ l1_orders_2(sK0)
    | spl5_33 ),
    inference(resolution,[],[f295,f53])).

fof(f295,plain,
    ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | spl5_33 ),
    inference(avatar_component_clause,[],[f293])).

fof(f296,plain,
    ( ~ spl5_33
    | spl5_23 ),
    inference(avatar_split_clause,[],[f291,f227,f293])).

fof(f291,plain,
    ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | spl5_23 ),
    inference(resolution,[],[f229,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_relset_1)).

fof(f229,plain,
    ( ~ m1_subset_1(k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | spl5_23 ),
    inference(avatar_component_clause,[],[f227])).

fof(f234,plain,
    ( ~ spl5_23
    | spl5_24
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f225,f215,f231,f227])).

fof(f225,plain,
    ( v1_orders_2(k7_lattice3(sK0))
    | ~ m1_subset_1(k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl5_21 ),
    inference(superposition,[],[f63,f217])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_orders_2(g1_orders_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( l1_orders_2(g1_orders_2(X0,X1))
        & v1_orders_2(g1_orders_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ( l1_orders_2(g1_orders_2(X0,X1))
        & v1_orders_2(g1_orders_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_orders_2)).

fof(f218,plain,
    ( spl5_21
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f210,f76,f215])).

fof(f210,plain,
    ( k7_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl5_1 ),
    inference(resolution,[],[f54,f78])).

fof(f78,plain,
    ( l1_orders_2(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f54,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_lattice3)).

fof(f194,plain,
    ( ~ spl5_1
    | spl5_17 ),
    inference(avatar_split_clause,[],[f192,f183,f76])).

fof(f192,plain,
    ( ~ l1_orders_2(sK0)
    | spl5_17 ),
    inference(resolution,[],[f185,f56])).

fof(f56,plain,(
    ! [X0] :
      ( l1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( l1_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( l1_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattice3)).

fof(f185,plain,
    ( ~ l1_orders_2(k7_lattice3(sK0))
    | spl5_17 ),
    inference(avatar_component_clause,[],[f183])).

fof(f151,plain,
    ( spl5_12
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f144,f76,f148])).

fof(f144,plain,
    ( u1_orders_2(sK0) = k4_relat_1(k4_relat_1(u1_orders_2(sK0)))
    | ~ spl5_1 ),
    inference(resolution,[],[f131,f78])).

fof(f131,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | u1_orders_2(X0) = k4_relat_1(k4_relat_1(u1_orders_2(X0))) ) ),
    inference(resolution,[],[f101,f53])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    inference(resolution,[],[f69,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(f130,plain,
    ( spl5_9
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f125,f121,f110,f127])).

fof(f110,plain,
    ( spl5_6
  <=> sK1 = k8_lattice3(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f121,plain,
    ( spl5_8
  <=> r1_orders_2(k7_lattice3(sK0),sK2,k8_lattice3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f125,plain,
    ( r1_orders_2(k7_lattice3(sK0),sK2,sK1)
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f123,f112])).

fof(f112,plain,
    ( sK1 = k8_lattice3(sK0,sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f110])).

fof(f123,plain,
    ( r1_orders_2(k7_lattice3(sK0),sK2,k8_lattice3(sK0,sK1))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f121])).

fof(f124,plain,
    ( spl5_8
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f119,f115,f95,f121])).

fof(f95,plain,
    ( spl5_5
  <=> r1_orders_2(k7_lattice3(sK0),k8_lattice3(sK0,sK2),k8_lattice3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f115,plain,
    ( spl5_7
  <=> sK2 = k8_lattice3(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f119,plain,
    ( r1_orders_2(k7_lattice3(sK0),sK2,k8_lattice3(sK0,sK1))
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(backward_demodulation,[],[f96,f117])).

fof(f117,plain,
    ( sK2 = k8_lattice3(sK0,sK2)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f115])).

fof(f96,plain,
    ( r1_orders_2(k7_lattice3(sK0),k8_lattice3(sK0,sK2),k8_lattice3(sK0,sK1))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f95])).

fof(f118,plain,
    ( spl5_7
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f108,f86,f76,f115])).

fof(f108,plain,
    ( sK2 = k8_lattice3(sK0,sK2)
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(resolution,[],[f104,f88])).

fof(f88,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f104,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k8_lattice3(sK0,X0) = X0 )
    | ~ spl5_1 ),
    inference(resolution,[],[f58,f78])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k8_lattice3(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k8_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k8_lattice3(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_lattice3)).

fof(f113,plain,
    ( spl5_6
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f107,f81,f76,f110])).

fof(f107,plain,
    ( sK1 = k8_lattice3(sK0,sK1)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f104,f83])).

fof(f83,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f99,plain,
    ( spl5_4
    | spl5_5 ),
    inference(avatar_split_clause,[],[f43,f95,f91])).

fof(f43,plain,
    ( r1_orders_2(k7_lattice3(sK0),k8_lattice3(sK0,sK2),k8_lattice3(sK0,sK1))
    | r1_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <~> r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,X2),k8_lattice3(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r1_orders_2(X0,X1,X2)
                <=> r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,X2),k8_lattice3(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,X2),k8_lattice3(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_lattice3)).

fof(f98,plain,
    ( ~ spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f44,f95,f91])).

fof(f44,plain,
    ( ~ r1_orders_2(k7_lattice3(sK0),k8_lattice3(sK0,sK2),k8_lattice3(sK0,sK1))
    | ~ r1_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f89,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f45,f86])).

fof(f45,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f84,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f46,f81])).

fof(f46,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f79,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f47,f76])).

fof(f47,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f21])).

%------------------------------------------------------------------------------
