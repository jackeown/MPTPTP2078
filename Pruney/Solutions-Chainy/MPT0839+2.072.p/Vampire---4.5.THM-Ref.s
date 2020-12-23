%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 134 expanded)
%              Number of leaves         :   23 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :  206 ( 350 expanded)
%              Number of equality atoms :   27 (  52 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f119,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f49,f55,f61,f69,f77,f84,f92,f103,f110,f117,f118])).

fof(f118,plain,
    ( ~ spl5_12
    | ~ spl5_6
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f111,f107,f74,f114])).

fof(f114,plain,
    ( spl5_12
  <=> m1_subset_1(sK3(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f74,plain,
    ( spl5_6
  <=> k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f107,plain,
    ( spl5_11
  <=> r2_hidden(sK3(sK2),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f111,plain,
    ( ~ m1_subset_1(sK3(sK2),sK1)
    | ~ spl5_6
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f109,f79])).

fof(f79,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,sK1)
        | ~ r2_hidden(X3,k1_relat_1(sK2)) )
    | ~ spl5_6 ),
    inference(backward_demodulation,[],[f31,f76])).

fof(f76,plain,
    ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f74])).

fof(f31,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK1)
      | ~ r2_hidden(X3,k1_relset_1(sK1,sK0,sK2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_relset_1(sK1,sK0,sK2))
        | ~ m1_subset_1(X3,sK1) )
    & k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( ! [X3] :
            ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
            | ~ m1_subset_1(X3,X1) )
        & k1_xboole_0 != k2_relset_1(X1,X0,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ! [X3] :
          ( ~ r2_hidden(X3,k1_relset_1(sK1,sK0,sK2))
          | ~ m1_subset_1(X3,sK1) )
      & k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
          | ~ m1_subset_1(X3,X1) )
      & k1_xboole_0 != k2_relset_1(X1,X0,X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
          | ~ m1_subset_1(X3,X1) )
      & k1_xboole_0 != k2_relset_1(X1,X0,X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ~ ( ! [X3] :
                ( m1_subset_1(X3,X1)
               => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
            & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,X1)
                       => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
                    & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
                  & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).

fof(f109,plain,
    ( r2_hidden(sK3(sK2),k1_relat_1(sK2))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f107])).

fof(f117,plain,
    ( spl5_12
    | ~ spl5_7
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f112,f107,f81,f114])).

fof(f81,plain,
    ( spl5_7
  <=> m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f112,plain,
    ( m1_subset_1(sK3(sK2),sK1)
    | ~ spl5_7
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f83,f109,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f83,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f81])).

fof(f110,plain,
    ( spl5_11
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f105,f100,f58,f107])).

fof(f58,plain,
    ( spl5_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f100,plain,
    ( spl5_10
  <=> r2_hidden(sK4(k2_relat_1(sK2)),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f105,plain,
    ( r2_hidden(sK3(sK2),k1_relat_1(sK2))
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f60,f102,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f25])).

fof(f25,plain,(
    ! [X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
     => r2_hidden(sK3(X1),k1_relat_1(X1)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).

fof(f102,plain,
    ( r2_hidden(sK4(k2_relat_1(sK2)),k2_relat_1(sK2))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f100])).

fof(f60,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f58])).

fof(f103,plain,
    ( spl5_10
    | ~ spl5_3
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f98,f89,f52,f100])).

fof(f52,plain,
    ( spl5_3
  <=> r2_hidden(sK4(k2_relset_1(sK1,sK0,sK2)),k2_relset_1(sK1,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f89,plain,
    ( spl5_8
  <=> k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f98,plain,
    ( r2_hidden(sK4(k2_relat_1(sK2)),k2_relat_1(sK2))
    | ~ spl5_3
    | ~ spl5_8 ),
    inference(backward_demodulation,[],[f54,f91])).

fof(f91,plain,
    ( k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f89])).

fof(f54,plain,
    ( r2_hidden(sK4(k2_relset_1(sK1,sK0,sK2)),k2_relset_1(sK1,sK0,sK2))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f92,plain,
    ( spl5_8
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f86,f46,f89])).

fof(f46,plain,
    ( spl5_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f86,plain,
    ( k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f48,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f48,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f84,plain,
    ( spl5_7
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f78,f74,f66,f81])).

fof(f66,plain,
    ( spl5_5
  <=> m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f78,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(backward_demodulation,[],[f68,f76])).

fof(f68,plain,
    ( m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(sK1))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f66])).

fof(f77,plain,
    ( spl5_6
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f70,f46,f74])).

fof(f70,plain,
    ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f48,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f69,plain,
    ( spl5_5
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f63,f46,f66])).

fof(f63,plain,
    ( m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(sK1))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f48,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f61,plain,
    ( spl5_4
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f56,f46,f58])).

fof(f56,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f39,f48,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

% (20897)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% (20888)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% (20893)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% (20898)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% (20901)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% (20891)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% (20890)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% (20892)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% (20891)Refutation not found, incomplete strategy% (20891)------------------------------
% (20891)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (20891)Termination reason: Refutation not found, incomplete strategy

% (20891)Memory used [KB]: 10490
% (20891)Time elapsed: 0.069 s
% (20891)------------------------------
% (20891)------------------------------
fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f39,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f55,plain,
    ( spl5_3
    | spl5_1 ),
    inference(avatar_split_clause,[],[f50,f41,f52])).

fof(f41,plain,
    ( spl5_1
  <=> k1_xboole_0 = k2_relset_1(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f50,plain,
    ( r2_hidden(sK4(k2_relset_1(sK1,sK0,sK2)),k2_relset_1(sK1,sK0,sK2))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f43,f34])).

fof(f34,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

% (20909)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% (20903)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% (20910)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% (20904)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% (20907)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% (20908)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% (20908)Refutation not found, incomplete strategy% (20908)------------------------------
% (20908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (20908)Termination reason: Refutation not found, incomplete strategy

% (20908)Memory used [KB]: 6140
% (20908)Time elapsed: 0.110 s
% (20908)------------------------------
% (20908)------------------------------
% (20900)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% (20899)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% (20896)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% (20889)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% (20911)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% (20896)Refutation not found, incomplete strategy% (20896)------------------------------
% (20896)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (20896)Termination reason: Refutation not found, incomplete strategy

% (20896)Memory used [KB]: 10618
% (20896)Time elapsed: 0.107 s
% (20896)------------------------------
% (20896)------------------------------
% (20905)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
fof(f43,plain,
    ( k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f49,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f29,f46])).

fof(f29,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f44,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f30,f41])).

fof(f30,plain,(
    k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:27:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (20894)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.49  % (20894)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f44,f49,f55,f61,f69,f77,f84,f92,f103,f110,f117,f118])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    ~spl5_12 | ~spl5_6 | ~spl5_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f111,f107,f74,f114])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    spl5_12 <=> m1_subset_1(sK3(sK2),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    spl5_6 <=> k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    spl5_11 <=> r2_hidden(sK3(sK2),k1_relat_1(sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    ~m1_subset_1(sK3(sK2),sK1) | (~spl5_6 | ~spl5_11)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f109,f79])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    ( ! [X3] : (~m1_subset_1(X3,sK1) | ~r2_hidden(X3,k1_relat_1(sK2))) ) | ~spl5_6),
% 0.21/0.49    inference(backward_demodulation,[],[f31,f76])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) | ~spl5_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f74])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X3] : (~m1_subset_1(X3,sK1) | ~r2_hidden(X3,k1_relset_1(sK1,sK0,sK2))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,sK2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => (! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,sK2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.49    inference(flattening,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ? [X0,X1,X2] : ((! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))),
% 0.21/0.49    inference(pure_predicate_removal,[],[f10])).
% 0.21/0.49  fof(f10,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 0.21/0.49    inference(negated_conjecture,[],[f9])).
% 0.21/0.49  fof(f9,conjecture,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    r2_hidden(sK3(sK2),k1_relat_1(sK2)) | ~spl5_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f107])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    spl5_12 | ~spl5_7 | ~spl5_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f112,f107,f81,f114])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    spl5_7 <=> m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    m1_subset_1(sK3(sK2),sK1) | (~spl5_7 | ~spl5_11)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f83,f109,f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) | ~spl5_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f81])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    spl5_11 | ~spl5_4 | ~spl5_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f105,f100,f58,f107])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    spl5_4 <=> v1_relat_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    spl5_10 <=> r2_hidden(sK4(k2_relat_1(sK2)),k2_relat_1(sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    r2_hidden(sK3(sK2),k1_relat_1(sK2)) | (~spl5_4 | ~spl5_10)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f60,f102,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(sK3(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1] : (r2_hidden(sK3(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(sK3(X1),k1_relat_1(X1)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0,X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k1_relat_1(X1)) & r2_hidden(X0,k2_relat_1(X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    r2_hidden(sK4(k2_relat_1(sK2)),k2_relat_1(sK2)) | ~spl5_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f100])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    v1_relat_1(sK2) | ~spl5_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f58])).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    spl5_10 | ~spl5_3 | ~spl5_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f98,f89,f52,f100])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    spl5_3 <=> r2_hidden(sK4(k2_relset_1(sK1,sK0,sK2)),k2_relset_1(sK1,sK0,sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    spl5_8 <=> k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    r2_hidden(sK4(k2_relat_1(sK2)),k2_relat_1(sK2)) | (~spl5_3 | ~spl5_8)),
% 0.21/0.49    inference(backward_demodulation,[],[f54,f91])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) | ~spl5_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f89])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    r2_hidden(sK4(k2_relset_1(sK1,sK0,sK2)),k2_relset_1(sK1,sK0,sK2)) | ~spl5_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f52])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    spl5_8 | ~spl5_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f86,f46,f89])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    spl5_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) | ~spl5_2),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f48,f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl5_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f46])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    spl5_7 | ~spl5_5 | ~spl5_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f78,f74,f66,f81])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    spl5_5 <=> m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) | (~spl5_5 | ~spl5_6)),
% 0.21/0.49    inference(backward_demodulation,[],[f68,f76])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(sK1)) | ~spl5_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f66])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    spl5_6 | ~spl5_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f70,f46,f74])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) | ~spl5_2),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f48,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    spl5_5 | ~spl5_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f63,f46,f66])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(sK1)) | ~spl5_2),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f48,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    spl5_4 | ~spl5_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f56,f46,f58])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    v1_relat_1(sK2) | ~spl5_2),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f39,f48,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  % (20897)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.49  % (20888)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.50  % (20893)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.50  % (20898)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.50  % (20901)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.50  % (20891)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.50  % (20890)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.50  % (20892)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.50  % (20891)Refutation not found, incomplete strategy% (20891)------------------------------
% 0.21/0.50  % (20891)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (20891)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (20891)Memory used [KB]: 10490
% 0.21/0.50  % (20891)Time elapsed: 0.069 s
% 0.21/0.50  % (20891)------------------------------
% 0.21/0.50  % (20891)------------------------------
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    spl5_3 | spl5_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f50,f41,f52])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    spl5_1 <=> k1_xboole_0 = k2_relset_1(sK1,sK0,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    r2_hidden(sK4(k2_relset_1(sK1,sK0,sK2)),k2_relset_1(sK1,sK0,sK2)) | spl5_1),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f43,f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.51  % (20909)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.51  % (20903)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.51  % (20910)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.51  % (20904)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.51  % (20907)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.51  % (20908)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.51  % (20908)Refutation not found, incomplete strategy% (20908)------------------------------
% 0.21/0.51  % (20908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (20908)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (20908)Memory used [KB]: 6140
% 0.21/0.51  % (20908)Time elapsed: 0.110 s
% 0.21/0.51  % (20908)------------------------------
% 0.21/0.51  % (20908)------------------------------
% 0.21/0.51  % (20900)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.51  % (20899)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.51  % (20896)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.51  % (20889)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.51  % (20911)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.51  % (20896)Refutation not found, incomplete strategy% (20896)------------------------------
% 0.21/0.51  % (20896)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (20896)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (20896)Memory used [KB]: 10618
% 0.21/0.51  % (20896)Time elapsed: 0.107 s
% 0.21/0.51  % (20896)------------------------------
% 0.21/0.51  % (20896)------------------------------
% 0.21/0.51  % (20905)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) | spl5_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f41])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    spl5_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f29,f46])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ~spl5_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f30,f41])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (20894)------------------------------
% 0.21/0.52  % (20894)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (20894)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (20894)Memory used [KB]: 10618
% 0.21/0.52  % (20894)Time elapsed: 0.082 s
% 0.21/0.52  % (20894)------------------------------
% 0.21/0.52  % (20894)------------------------------
% 0.21/0.52  % (20911)Refutation not found, incomplete strategy% (20911)------------------------------
% 0.21/0.52  % (20911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (20911)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (20911)Memory used [KB]: 10618
% 0.21/0.52  % (20911)Time elapsed: 0.063 s
% 0.21/0.52  % (20911)------------------------------
% 0.21/0.52  % (20911)------------------------------
% 0.21/0.52  % (20887)Success in time 0.157 s
%------------------------------------------------------------------------------
