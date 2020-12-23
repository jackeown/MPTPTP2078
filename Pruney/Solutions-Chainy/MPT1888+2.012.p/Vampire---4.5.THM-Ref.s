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
% DateTime   : Thu Dec  3 13:22:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 297 expanded)
%              Number of leaves         :   32 ( 134 expanded)
%              Depth                    :   11
%              Number of atoms          :  546 (1396 expanded)
%              Number of equality atoms :   64 ( 171 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f397,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f60,f64,f68,f72,f76,f80,f84,f93,f99,f106,f118,f123,f134,f141,f172,f203,f247,f297,f350,f372])).

fof(f372,plain,
    ( ~ spl4_3
    | spl4_16
    | ~ spl4_11
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f357,f348,f104,f132,f62])).

fof(f62,plain,
    ( spl4_3
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f132,plain,
    ( spl4_16
  <=> k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK2))) = k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f104,plain,
    ( spl4_11
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | u1_struct_0(k1_tex_2(sK0,X0)) = k6_domain_1(u1_struct_0(sK0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f348,plain,
    ( spl4_46
  <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f357,plain,
    ( k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK2))) = k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl4_11
    | ~ spl4_46 ),
    inference(superposition,[],[f349,f105])).

fof(f105,plain,
    ( ! [X0] :
        ( u1_struct_0(k1_tex_2(sK0,X0)) = k6_domain_1(u1_struct_0(sK0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f104])).

fof(f349,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f348])).

fof(f350,plain,
    ( spl4_14
    | ~ spl4_3
    | spl4_46
    | ~ spl4_17
    | ~ spl4_24
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f346,f216,f201,f139,f348,f62,f121])).

fof(f121,plain,
    ( spl4_14
  <=> r1_xboole_0(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f139,plain,
    ( spl4_17
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f201,plain,
    ( spl4_24
  <=> k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1))) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f216,plain,
    ( spl4_26
  <=> m1_subset_1(sK3(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f346,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_xboole_0(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | ~ spl4_17
    | ~ spl4_24
    | ~ spl4_26 ),
    inference(forward_demodulation,[],[f344,f202])).

fof(f202,plain,
    ( k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1))) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f201])).

fof(f344,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_xboole_0(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | ~ spl4_17
    | ~ spl4_26 ),
    inference(resolution,[],[f334,f143])).

fof(f143,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK3(X3,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))),u1_struct_0(sK0))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3(X3,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_xboole_0(X3,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) )
    | ~ spl4_17 ),
    inference(resolution,[],[f140,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

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
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f140,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f139])).

fof(f334,plain,
    ( m1_subset_1(sK3(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))),u1_struct_0(sK0))
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f216])).

fof(f297,plain,
    ( spl4_14
    | ~ spl4_4
    | ~ spl4_10
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f294,f245,f97,f66,f121])).

fof(f66,plain,
    ( spl4_4
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f97,plain,
    ( spl4_10
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_subset_1(u1_struct_0(k1_tex_2(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f245,plain,
    ( spl4_33
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK3(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))),k2_pre_topc(sK0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f294,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_xboole_0(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | ~ spl4_10
    | ~ spl4_33 ),
    inference(resolution,[],[f270,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f270,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))),k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X0))))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl4_10
    | ~ spl4_33 ),
    inference(resolution,[],[f246,f98])).

fof(f98,plain,
    ( ! [X0] :
        ( m1_subset_1(u1_struct_0(k1_tex_2(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f97])).

fof(f246,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK3(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))),k2_pre_topc(sK0,X1)) )
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f245])).

fof(f247,plain,
    ( spl4_33
    | ~ spl4_5
    | spl4_26 ),
    inference(avatar_split_clause,[],[f242,f216,f70,f245])).

fof(f70,plain,
    ( spl4_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f242,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK3(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))),k2_pre_topc(sK0,X1)) )
    | spl4_26 ),
    inference(resolution,[],[f217,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X2,k2_pre_topc(X1,X0)) ) ),
    inference(resolution,[],[f50,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

% (12033)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f217,plain,
    ( ~ m1_subset_1(sK3(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))),u1_struct_0(sK0))
    | spl4_26 ),
    inference(avatar_component_clause,[],[f216])).

fof(f203,plain,
    ( ~ spl4_4
    | spl4_24
    | ~ spl4_10
    | spl4_14
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f197,f170,f121,f97,f201,f66])).

fof(f170,plain,
    ( spl4_20
  <=> ! [X3,X5,X4] :
        ( k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X3))) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X3))),X4)))
        | ~ r2_hidden(sK3(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X3))),X4),k2_pre_topc(sK0,X5))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_xboole_0(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X3))),X4)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f197,plain,
    ( k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1))) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_10
    | spl4_14
    | ~ spl4_20 ),
    inference(resolution,[],[f196,f122])).

fof(f122,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | spl4_14 ),
    inference(avatar_component_clause,[],[f121])).

fof(f196,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X0))),X1)
        | k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X0))) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X0))),X1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl4_10
    | ~ spl4_20 ),
    inference(duplicate_literal_removal,[],[f195])).

fof(f195,plain,
    ( ! [X0,X1] :
        ( k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X0))) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X0))),X1)))
        | r1_xboole_0(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X0))),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl4_10
    | ~ spl4_20 ),
    inference(resolution,[],[f194,f98])).

fof(f194,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(u1_struct_0(k1_tex_2(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X0))) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X0))),X1)))
        | r1_xboole_0(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X0))),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl4_20 ),
    inference(duplicate_literal_removal,[],[f191])).

fof(f191,plain,
    ( ! [X0,X1] :
        ( k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X0))) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X0))),X1)))
        | ~ m1_subset_1(u1_struct_0(k1_tex_2(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_xboole_0(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X0))),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_xboole_0(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X0))),X1) )
    | ~ spl4_20 ),
    inference(resolution,[],[f171,f44])).

fof(f171,plain,
    ( ! [X4,X5,X3] :
        ( ~ r2_hidden(sK3(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X3))),X4),k2_pre_topc(sK0,X5))
        | k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X3))) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X3))),X4)))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_xboole_0(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X3))),X4)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f170])).

fof(f172,plain,
    ( ~ spl4_5
    | spl4_20
    | ~ spl4_11
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f168,f139,f104,f170,f70])).

fof(f168,plain,
    ( ! [X4,X5,X3] :
        ( k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X3))) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X3))),X4)))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_xboole_0(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X3))),X4)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK3(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X3))),X4),k2_pre_topc(sK0,X5)) )
    | ~ spl4_11
    | ~ spl4_17 ),
    inference(resolution,[],[f146,f101])).

fof(f146,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK3(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X0))),X1),u1_struct_0(sK0))
        | k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X0))) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X0))),X1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_xboole_0(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X0))),X1) )
    | ~ spl4_11
    | ~ spl4_17 ),
    inference(resolution,[],[f145,f44])).

fof(f145,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X0))))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl4_11
    | ~ spl4_17 ),
    inference(duplicate_literal_removal,[],[f144])).

fof(f144,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X0))))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl4_11
    | ~ spl4_17 ),
    inference(superposition,[],[f140,f105])).

fof(f141,plain,
    ( spl4_8
    | ~ spl4_7
    | ~ spl4_5
    | spl4_17
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f136,f74,f139,f70,f78,f82])).

fof(f82,plain,
    ( spl4_8
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f78,plain,
    ( spl4_7
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f74,plain,
    ( spl4_6
  <=> v3_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f136,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_6 ),
    inference(resolution,[],[f41,f75])).

fof(f75,plain,
    ( v3_tdlat_3(sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f74])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_tdlat_3(X0)
      | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
              | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
              | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
               => k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tex_2)).

fof(f134,plain,
    ( ~ spl4_4
    | ~ spl4_16
    | ~ spl4_11
    | spl4_13 ),
    inference(avatar_split_clause,[],[f130,f116,f104,f132,f66])).

fof(f116,plain,
    ( spl4_13
  <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f130,plain,
    ( k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK2))) != k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_11
    | spl4_13 ),
    inference(superposition,[],[f117,f105])).

fof(f117,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK2)))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f116])).

fof(f123,plain,
    ( ~ spl4_4
    | ~ spl4_14
    | spl4_2
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f109,f104,f58,f121,f66])).

fof(f58,plain,
    ( spl4_2
  <=> r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f109,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl4_2
    | ~ spl4_11 ),
    inference(superposition,[],[f59,f105])).

fof(f59,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f118,plain,
    ( ~ spl4_3
    | ~ spl4_13
    | spl4_1
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f108,f104,f54,f116,f62])).

fof(f54,plain,
    ( spl4_1
  <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f108,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK2)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | spl4_1
    | ~ spl4_11 ),
    inference(superposition,[],[f55,f105])).

fof(f55,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f106,plain,
    ( spl4_8
    | spl4_11
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f102,f70,f104,f82])).

fof(f102,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | u1_struct_0(k1_tex_2(sK0,X0)) = k6_domain_1(u1_struct_0(sK0),X0)
        | v2_struct_0(sK0) )
    | ~ spl4_5 ),
    inference(resolution,[],[f87,f71])).

fof(f71,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f70])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f86,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(f86,plain,(
    ! [X0,X1] :
      ( k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1))
      | v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f85,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1))
      | ~ v1_pre_topc(k1_tex_2(X0,X1))
      | v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f52,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_pre_topc(k1_tex_2(X0,X1),X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1))
      | ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ v1_pre_topc(k1_tex_2(X0,X1))
      | v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)
      | k1_tex_2(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_tex_2(X0,X1) = X2
                  | u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1) )
                & ( u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)
                  | k1_tex_2(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tex_2)).

fof(f99,plain,
    ( ~ spl4_5
    | spl4_10
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f94,f91,f97,f70])).

fof(f91,plain,
    ( spl4_9
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_pre_topc(k1_tex_2(sK0,X0),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f94,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_subset_1(u1_struct_0(k1_tex_2(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl4_9 ),
    inference(resolution,[],[f92,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f92,plain,
    ( ! [X0] :
        ( m1_pre_topc(k1_tex_2(sK0,X0),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f91])).

fof(f93,plain,
    ( spl4_8
    | spl4_9
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f88,f70,f91,f82])).

fof(f88,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_pre_topc(k1_tex_2(sK0,X0),sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_5 ),
    inference(resolution,[],[f49,f71])).

fof(f84,plain,(
    ~ spl4_8 ),
    inference(avatar_split_clause,[],[f32,f82])).

fof(f32,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))
    & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v3_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f27,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
                & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))
              & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v3_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))
            & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
          & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X2] :
        ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
        & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))
      & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
              & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
              & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
                  | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
                | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tex_2)).

fof(f80,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f33,f78])).

fof(f33,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f76,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f34,f74])).

fof(f34,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f72,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f35,f70])).

fof(f35,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f68,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f36,f66])).

fof(f36,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f64,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f37,f62])).

fof(f37,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f60,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f38,f58])).

fof(f38,plain,(
    ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    inference(cnf_transformation,[],[f28])).

fof(f56,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f39,f54])).

fof(f39,plain,(
    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:15:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (12042)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (12034)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (12048)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.48  % (12050)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (12032)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (12035)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (12029)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (12050)Refutation not found, incomplete strategy% (12050)------------------------------
% 0.21/0.48  % (12050)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (12040)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  % (12050)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (12050)Memory used [KB]: 10618
% 0.21/0.49  % (12050)Time elapsed: 0.059 s
% 0.21/0.49  % (12050)------------------------------
% 0.21/0.49  % (12050)------------------------------
% 0.21/0.49  % (12031)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (12036)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (12047)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % (12030)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (12045)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (12039)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.51  % (12035)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f397,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f56,f60,f64,f68,f72,f76,f80,f84,f93,f99,f106,f118,f123,f134,f141,f172,f203,f247,f297,f350,f372])).
% 0.21/0.51  fof(f372,plain,(
% 0.21/0.51    ~spl4_3 | spl4_16 | ~spl4_11 | ~spl4_46),
% 0.21/0.51    inference(avatar_split_clause,[],[f357,f348,f104,f132,f62])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    spl4_3 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    spl4_16 <=> k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK2))) = k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    spl4_11 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | u1_struct_0(k1_tex_2(sK0,X0)) = k6_domain_1(u1_struct_0(sK0),X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.51  fof(f348,plain,(
% 0.21/0.51    spl4_46 <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 0.21/0.51  fof(f357,plain,(
% 0.21/0.51    k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK2))) = k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1))) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | (~spl4_11 | ~spl4_46)),
% 0.21/0.51    inference(superposition,[],[f349,f105])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    ( ! [X0] : (u1_struct_0(k1_tex_2(sK0,X0)) = k6_domain_1(u1_struct_0(sK0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl4_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f104])).
% 0.21/0.51  fof(f349,plain,(
% 0.21/0.51    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1))) | ~spl4_46),
% 0.21/0.51    inference(avatar_component_clause,[],[f348])).
% 0.21/0.51  fof(f350,plain,(
% 0.21/0.51    spl4_14 | ~spl4_3 | spl4_46 | ~spl4_17 | ~spl4_24 | ~spl4_26),
% 0.21/0.51    inference(avatar_split_clause,[],[f346,f216,f201,f139,f348,f62,f121])).
% 0.21/0.51  fof(f121,plain,(
% 0.21/0.51    spl4_14 <=> r1_xboole_0(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.51  fof(f139,plain,(
% 0.21/0.51    spl4_17 <=> ! [X1,X0] : (~r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.21/0.51  fof(f201,plain,(
% 0.21/0.51    spl4_24 <=> k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1))) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.21/0.51  fof(f216,plain,(
% 0.21/0.51    spl4_26 <=> m1_subset_1(sK3(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))),u1_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.21/0.51  fof(f346,plain,(
% 0.21/0.51    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1))) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | r1_xboole_0(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | (~spl4_17 | ~spl4_24 | ~spl4_26)),
% 0.21/0.51    inference(forward_demodulation,[],[f344,f202])).
% 0.21/0.51  fof(f202,plain,(
% 0.21/0.51    k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1))) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))))) | ~spl4_24),
% 0.21/0.51    inference(avatar_component_clause,[],[f201])).
% 0.21/0.51  fof(f344,plain,(
% 0.21/0.51    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))))) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | r1_xboole_0(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | (~spl4_17 | ~spl4_26)),
% 0.21/0.51    inference(resolution,[],[f334,f143])).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~m1_subset_1(sK3(X3,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))),u1_struct_0(sK0)) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3(X3,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r1_xboole_0(X3,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))) ) | ~spl4_17),
% 0.21/0.51    inference(resolution,[],[f140,f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(rectify,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.51  fof(f140,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl4_17),
% 0.21/0.51    inference(avatar_component_clause,[],[f139])).
% 0.21/0.51  fof(f334,plain,(
% 0.21/0.51    m1_subset_1(sK3(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))),u1_struct_0(sK0)) | ~spl4_26),
% 0.21/0.51    inference(avatar_component_clause,[],[f216])).
% 0.21/0.51  fof(f297,plain,(
% 0.21/0.51    spl4_14 | ~spl4_4 | ~spl4_10 | ~spl4_33),
% 0.21/0.51    inference(avatar_split_clause,[],[f294,f245,f97,f66,f121])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    spl4_4 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    spl4_10 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(u1_struct_0(k1_tex_2(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.51  fof(f245,plain,(
% 0.21/0.51    spl4_33 <=> ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK3(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))),k2_pre_topc(sK0,X1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 0.21/0.51  fof(f294,plain,(
% 0.21/0.51    ~m1_subset_1(sK1,u1_struct_0(sK0)) | r1_xboole_0(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | (~spl4_10 | ~spl4_33)),
% 0.21/0.51    inference(resolution,[],[f270,f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f270,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(sK3(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))),k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X0)))) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl4_10 | ~spl4_33)),
% 0.21/0.51    inference(resolution,[],[f246,f98])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(u1_struct_0(k1_tex_2(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl4_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f97])).
% 0.21/0.51  fof(f246,plain,(
% 0.21/0.51    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK3(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))),k2_pre_topc(sK0,X1))) ) | ~spl4_33),
% 0.21/0.51    inference(avatar_component_clause,[],[f245])).
% 0.21/0.51  fof(f247,plain,(
% 0.21/0.51    spl4_33 | ~spl4_5 | spl4_26),
% 0.21/0.51    inference(avatar_split_clause,[],[f242,f216,f70,f245])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    spl4_5 <=> l1_pre_topc(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.51  fof(f242,plain,(
% 0.21/0.51    ( ! [X1] : (~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK3(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))),k2_pre_topc(sK0,X1))) ) | spl4_26),
% 0.21/0.51    inference(resolution,[],[f217,f101])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~r2_hidden(X2,k2_pre_topc(X1,X0))) )),
% 0.21/0.51    inference(resolution,[],[f50,f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  % (12033)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.51    inference(flattening,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.21/0.51  fof(f217,plain,(
% 0.21/0.51    ~m1_subset_1(sK3(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))),u1_struct_0(sK0)) | spl4_26),
% 0.21/0.51    inference(avatar_component_clause,[],[f216])).
% 0.21/0.51  fof(f203,plain,(
% 0.21/0.51    ~spl4_4 | spl4_24 | ~spl4_10 | spl4_14 | ~spl4_20),
% 0.21/0.51    inference(avatar_split_clause,[],[f197,f170,f121,f97,f201,f66])).
% 0.21/0.51  fof(f170,plain,(
% 0.21/0.51    spl4_20 <=> ! [X3,X5,X4] : (k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X3))) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X3))),X4))) | ~r2_hidden(sK3(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X3))),X4),k2_pre_topc(sK0,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X3))),X4) | ~m1_subset_1(X3,u1_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.21/0.51  fof(f197,plain,(
% 0.21/0.51    k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1))) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl4_10 | spl4_14 | ~spl4_20)),
% 0.21/0.51    inference(resolution,[],[f196,f122])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    ~r1_xboole_0(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | spl4_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f121])).
% 0.21/0.51  fof(f196,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_xboole_0(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X0))),X1) | k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X0))) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X0))),X1))) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl4_10 | ~spl4_20)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f195])).
% 0.21/0.51  fof(f195,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X0))) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X0))),X1))) | r1_xboole_0(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X0))),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl4_10 | ~spl4_20)),
% 0.21/0.51    inference(resolution,[],[f194,f98])).
% 0.21/0.51  fof(f194,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(k1_tex_2(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X0))) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X0))),X1))) | r1_xboole_0(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X0))),X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl4_20),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f191])).
% 0.21/0.51  fof(f191,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X0))) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X0))),X1))) | ~m1_subset_1(u1_struct_0(k1_tex_2(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X0))),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_xboole_0(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X0))),X1)) ) | ~spl4_20),
% 0.21/0.51    inference(resolution,[],[f171,f44])).
% 0.21/0.51  fof(f171,plain,(
% 0.21/0.51    ( ! [X4,X5,X3] : (~r2_hidden(sK3(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X3))),X4),k2_pre_topc(sK0,X5)) | k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X3))) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X3))),X4))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X3))),X4) | ~m1_subset_1(X3,u1_struct_0(sK0))) ) | ~spl4_20),
% 0.21/0.51    inference(avatar_component_clause,[],[f170])).
% 0.21/0.51  fof(f172,plain,(
% 0.21/0.51    ~spl4_5 | spl4_20 | ~spl4_11 | ~spl4_17),
% 0.21/0.51    inference(avatar_split_clause,[],[f168,f139,f104,f170,f70])).
% 0.21/0.51  fof(f168,plain,(
% 0.21/0.51    ( ! [X4,X5,X3] : (k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X3))) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X3))),X4))) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r1_xboole_0(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X3))),X4) | ~l1_pre_topc(sK0) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK3(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X3))),X4),k2_pre_topc(sK0,X5))) ) | (~spl4_11 | ~spl4_17)),
% 0.21/0.51    inference(resolution,[],[f146,f101])).
% 0.21/0.51  fof(f146,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(sK3(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X0))),X1),u1_struct_0(sK0)) | k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X0))) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X0))),X1))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_xboole_0(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X0))),X1)) ) | (~spl4_11 | ~spl4_17)),
% 0.21/0.51    inference(resolution,[],[f145,f44])).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X1,k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X0)))) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl4_11 | ~spl4_17)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f144])).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X1,k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X0)))) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,X0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl4_11 | ~spl4_17)),
% 0.21/0.51    inference(superposition,[],[f140,f105])).
% 0.21/0.51  fof(f141,plain,(
% 0.21/0.51    spl4_8 | ~spl4_7 | ~spl4_5 | spl4_17 | ~spl4_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f136,f74,f139,f70,f78,f82])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    spl4_8 <=> v2_struct_0(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    spl4_7 <=> v2_pre_topc(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    spl4_6 <=> v3_tdlat_3(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl4_6),
% 0.21/0.51    inference(resolution,[],[f41,f75])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    v3_tdlat_3(sK0) | ~spl4_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f74])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v3_tdlat_3(X0) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) => k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tex_2)).
% 0.21/0.51  fof(f134,plain,(
% 0.21/0.51    ~spl4_4 | ~spl4_16 | ~spl4_11 | spl4_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f130,f116,f104,f132,f66])).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    spl4_13 <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK2)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.51  fof(f130,plain,(
% 0.21/0.51    k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK2))) != k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl4_11 | spl4_13)),
% 0.21/0.51    inference(superposition,[],[f117,f105])).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK2))) | spl4_13),
% 0.21/0.51    inference(avatar_component_clause,[],[f116])).
% 0.21/0.51  fof(f123,plain,(
% 0.21/0.51    ~spl4_4 | ~spl4_14 | spl4_2 | ~spl4_11),
% 0.21/0.51    inference(avatar_split_clause,[],[f109,f104,f58,f121,f66])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    spl4_2 <=> r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    ~r1_xboole_0(k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK1))),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (spl4_2 | ~spl4_11)),
% 0.21/0.51    inference(superposition,[],[f59,f105])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | spl4_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f58])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    ~spl4_3 | ~spl4_13 | spl4_1 | ~spl4_11),
% 0.21/0.51    inference(avatar_split_clause,[],[f108,f104,f54,f116,f62])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    spl4_1 <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,u1_struct_0(k1_tex_2(sK0,sK2))) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | (spl4_1 | ~spl4_11)),
% 0.21/0.51    inference(superposition,[],[f55,f105])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) | spl4_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f54])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    spl4_8 | spl4_11 | ~spl4_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f102,f70,f104,f82])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | u1_struct_0(k1_tex_2(sK0,X0)) = k6_domain_1(u1_struct_0(sK0),X0) | v2_struct_0(sK0)) ) | ~spl4_5),
% 0.21/0.51    inference(resolution,[],[f87,f71])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    l1_pre_topc(sK0) | ~spl4_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f70])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f86,f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) | v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f85,f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_pre_topc(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) | ~v1_pre_topc(k1_tex_2(X0,X1)) | v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f52,f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | m1_pre_topc(k1_tex_2(X0,X1),X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) | ~m1_pre_topc(k1_tex_2(X0,X1),X0) | ~v1_pre_topc(k1_tex_2(X0,X1)) | v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) | k1_tex_2(X0,X1) != X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (((k1_tex_2(X0,X1) = X2 | u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1)) & (u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) | k1_tex_2(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => (k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tex_2)).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    ~spl4_5 | spl4_10 | ~spl4_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f94,f91,f97,f70])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    spl4_9 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | m1_pre_topc(k1_tex_2(sK0,X0),sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(u1_struct_0(k1_tex_2(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl4_9),
% 0.21/0.51    inference(resolution,[],[f92,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    ( ! [X0] : (m1_pre_topc(k1_tex_2(sK0,X0),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl4_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f91])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    spl4_8 | spl4_9 | ~spl4_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f88,f70,f91,f82])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | m1_pre_topc(k1_tex_2(sK0,X0),sK0) | v2_struct_0(sK0)) ) | ~spl4_5),
% 0.21/0.51    inference(resolution,[],[f49,f71])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    ~spl4_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f32,f82])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ~v2_struct_0(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ((k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f27,f26,f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ? [X1] : (? [X2] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ? [X2] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & m1_subset_1(X2,u1_struct_0(sK0))) => (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : ((k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 0.21/0.51    inference(negated_conjecture,[],[f8])).
% 0.21/0.51  fof(f8,conjecture,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tex_2)).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    spl4_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f33,f78])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    v2_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    spl4_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f34,f74])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    v3_tdlat_3(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    spl4_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f35,f70])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    l1_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    spl4_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f36,f66])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    spl4_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f37,f62])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ~spl4_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f38,f58])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ~spl4_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f39,f54])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (12035)------------------------------
% 0.21/0.51  % (12035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (12035)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (12035)Memory used [KB]: 11001
% 0.21/0.51  % (12035)Time elapsed: 0.017 s
% 0.21/0.51  % (12035)------------------------------
% 0.21/0.51  % (12035)------------------------------
% 0.21/0.51  % (12043)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.51  % (12028)Success in time 0.152 s
%------------------------------------------------------------------------------
