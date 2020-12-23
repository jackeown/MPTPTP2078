%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:26 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 111 expanded)
%              Number of leaves         :   14 (  37 expanded)
%              Depth                    :   14
%              Number of atoms          :  215 ( 373 expanded)
%              Number of equality atoms :   17 (  29 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f257,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f56,f61,f67,f77,f180,f256])).

fof(f256,plain,
    ( ~ spl6_3
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7 ),
    inference(avatar_contradiction_clause,[],[f255])).

fof(f255,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7 ),
    inference(subsumption_resolution,[],[f250,f76])).

fof(f76,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl6_6
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f250,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl6_3
    | ~ spl6_5
    | spl6_7 ),
    inference(resolution,[],[f248,f70])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(sK5(X0,X1,sK3),X0),sK3)
        | ~ r2_hidden(X0,k9_relat_1(sK3,X1)) )
    | ~ spl6_5 ),
    inference(resolution,[],[f66,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f66,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl6_5
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f248,plain,
    ( ! [X3] : ~ r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),X3),sK3)
    | ~ spl6_3
    | spl6_7 ),
    inference(resolution,[],[f193,f55])).

fof(f55,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl6_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f193,plain,
    ( ! [X12,X10,X11] :
        ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(sK0,X12)))
        | ~ r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),X10),X11) )
    | spl6_7 ),
    inference(resolution,[],[f186,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f186,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),X0),k2_zfmisc_1(sK0,X1))
    | spl6_7 ),
    inference(resolution,[],[f179,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f179,plain,
    ( ~ r2_hidden(sK5(sK4,sK2,sK3),sK0)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl6_7
  <=> r2_hidden(sK5(sK4,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f180,plain,
    ( ~ spl6_7
    | ~ spl6_1
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f170,f74,f64,f40,f177])).

fof(f40,plain,
    ( spl6_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f170,plain,
    ( ~ r2_hidden(sK5(sK4,sK2,sK3),sK0)
    | ~ spl6_1
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f169,f76])).

fof(f169,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ r2_hidden(sK5(sK4,sK2,sK3),sK0)
    | ~ spl6_1
    | ~ spl6_5 ),
    inference(duplicate_literal_removal,[],[f165])).

fof(f165,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ r2_hidden(sK5(sK4,sK2,sK3),sK0)
    | ~ r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl6_1
    | ~ spl6_5 ),
    inference(resolution,[],[f158,f71])).

fof(f71,plain,
    ( ! [X2,X3] :
        ( r2_hidden(sK5(X2,X3,sK3),X3)
        | ~ r2_hidden(X2,k9_relat_1(sK3,X3)) )
    | ~ spl6_5 ),
    inference(resolution,[],[f66,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f158,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK4,X0,sK3),sK2)
        | ~ r2_hidden(sK4,k9_relat_1(sK3,X0))
        | ~ r2_hidden(sK5(sK4,X0,sK3),sK0) )
    | ~ spl6_1
    | ~ spl6_5 ),
    inference(equality_resolution,[],[f149])).

fof(f149,plain,
    ( ! [X0,X1] :
        ( sK4 != X0
        | ~ r2_hidden(sK5(X0,X1,sK3),sK2)
        | ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | ~ r2_hidden(sK5(X0,X1,sK3),sK0) )
    | ~ spl6_1
    | ~ spl6_5 ),
    inference(resolution,[],[f87,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f87,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK5(X2,X3,sK3),sK0)
        | ~ r2_hidden(sK5(X2,X3,sK3),sK2)
        | sK4 != X2
        | ~ r2_hidden(X2,k9_relat_1(sK3,X3)) )
    | ~ spl6_1
    | ~ spl6_5 ),
    inference(superposition,[],[f19,f85])).

fof(f85,plain,
    ( ! [X0,X1] :
        ( k1_funct_1(sK3,sK5(X0,X1,sK3)) = X0
        | ~ r2_hidden(X0,k9_relat_1(sK3,X1)) )
    | ~ spl6_1
    | ~ spl6_5 ),
    inference(resolution,[],[f70,f79])).

fof(f79,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK3)
        | k1_funct_1(sK3,X2) = X3 )
    | ~ spl6_1
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f45,f66])).

fof(f45,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(sK3)
        | k1_funct_1(sK3,X2) = X3
        | ~ r2_hidden(k4_tarski(X2,X3),sK3) )
    | ~ spl6_1 ),
    inference(resolution,[],[f42,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f42,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f19,plain,(
    ! [X5] :
      ( sK4 != k1_funct_1(sK3,X5)
      | ~ r2_hidden(X5,sK2)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ( m1_subset_1(X5,X0)
               => ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2) ) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).

fof(f77,plain,
    ( spl6_6
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f69,f58,f53,f74])).

fof(f58,plain,
    ( spl6_4
  <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f69,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f68,f55])).

fof(f68,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_4 ),
    inference(superposition,[],[f60,f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f60,plain,
    ( r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f58])).

fof(f67,plain,
    ( spl6_5
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f62,f53,f64])).

fof(f62,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_3 ),
    inference(resolution,[],[f55,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f61,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f20,f58])).

fof(f20,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f56,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f23,f53])).

fof(f23,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f11])).

fof(f43,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f21,f40])).

fof(f21,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n007.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 16:23:36 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.47  % (17127)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.49  % (17127)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % (17141)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.49  % (17131)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.49  % (17135)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.49  % (17130)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (17138)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  % (17137)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.50  % (17137)Refutation not found, incomplete strategy% (17137)------------------------------
% 0.22/0.50  % (17137)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (17137)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (17137)Memory used [KB]: 1663
% 0.22/0.50  % (17137)Time elapsed: 0.077 s
% 0.22/0.50  % (17137)------------------------------
% 0.22/0.50  % (17137)------------------------------
% 0.22/0.50  % (17126)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f257,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f43,f56,f61,f67,f77,f180,f256])).
% 0.22/0.50  fof(f256,plain,(
% 0.22/0.50    ~spl6_3 | ~spl6_5 | ~spl6_6 | spl6_7),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f255])).
% 0.22/0.50  fof(f255,plain,(
% 0.22/0.50    $false | (~spl6_3 | ~spl6_5 | ~spl6_6 | spl6_7)),
% 0.22/0.50    inference(subsumption_resolution,[],[f250,f76])).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~spl6_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f74])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    spl6_6 <=> r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.50  fof(f250,plain,(
% 0.22/0.50    ~r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (~spl6_3 | ~spl6_5 | spl6_7)),
% 0.22/0.50    inference(resolution,[],[f248,f70])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK5(X0,X1,sK3),X0),sK3) | ~r2_hidden(X0,k9_relat_1(sK3,X1))) ) | ~spl6_5),
% 0.22/0.50    inference(resolution,[],[f66,f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    v1_relat_1(sK3) | ~spl6_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f64])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    spl6_5 <=> v1_relat_1(sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.50  fof(f248,plain,(
% 0.22/0.50    ( ! [X3] : (~r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),X3),sK3)) ) | (~spl6_3 | spl6_7)),
% 0.22/0.50    inference(resolution,[],[f193,f55])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f53])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    spl6_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.50  fof(f193,plain,(
% 0.22/0.50    ( ! [X12,X10,X11] : (~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(sK0,X12))) | ~r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),X10),X11)) ) | spl6_7),
% 0.22/0.50    inference(resolution,[],[f186,f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.22/0.50  fof(f186,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),X0),k2_zfmisc_1(sK0,X1))) ) | spl6_7),
% 0.22/0.50    inference(resolution,[],[f179,f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.22/0.50  fof(f179,plain,(
% 0.22/0.50    ~r2_hidden(sK5(sK4,sK2,sK3),sK0) | spl6_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f177])).
% 0.22/0.50  fof(f177,plain,(
% 0.22/0.50    spl6_7 <=> r2_hidden(sK5(sK4,sK2,sK3),sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.50  fof(f180,plain,(
% 0.22/0.50    ~spl6_7 | ~spl6_1 | ~spl6_5 | ~spl6_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f170,f74,f64,f40,f177])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    spl6_1 <=> v1_funct_1(sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.50  fof(f170,plain,(
% 0.22/0.50    ~r2_hidden(sK5(sK4,sK2,sK3),sK0) | (~spl6_1 | ~spl6_5 | ~spl6_6)),
% 0.22/0.50    inference(subsumption_resolution,[],[f169,f76])).
% 0.22/0.50  fof(f169,plain,(
% 0.22/0.50    ~r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~r2_hidden(sK5(sK4,sK2,sK3),sK0) | (~spl6_1 | ~spl6_5)),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f165])).
% 0.22/0.50  fof(f165,plain,(
% 0.22/0.50    ~r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~r2_hidden(sK5(sK4,sK2,sK3),sK0) | ~r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (~spl6_1 | ~spl6_5)),
% 0.22/0.50    inference(resolution,[],[f158,f71])).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    ( ! [X2,X3] : (r2_hidden(sK5(X2,X3,sK3),X3) | ~r2_hidden(X2,k9_relat_1(sK3,X3))) ) | ~spl6_5),
% 0.22/0.50    inference(resolution,[],[f66,f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f158,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(sK5(sK4,X0,sK3),sK2) | ~r2_hidden(sK4,k9_relat_1(sK3,X0)) | ~r2_hidden(sK5(sK4,X0,sK3),sK0)) ) | (~spl6_1 | ~spl6_5)),
% 0.22/0.50    inference(equality_resolution,[],[f149])).
% 0.22/0.50  fof(f149,plain,(
% 0.22/0.50    ( ! [X0,X1] : (sK4 != X0 | ~r2_hidden(sK5(X0,X1,sK3),sK2) | ~r2_hidden(X0,k9_relat_1(sK3,X1)) | ~r2_hidden(sK5(X0,X1,sK3),sK0)) ) | (~spl6_1 | ~spl6_5)),
% 0.22/0.50    inference(resolution,[],[f87,f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    ( ! [X2,X3] : (~m1_subset_1(sK5(X2,X3,sK3),sK0) | ~r2_hidden(sK5(X2,X3,sK3),sK2) | sK4 != X2 | ~r2_hidden(X2,k9_relat_1(sK3,X3))) ) | (~spl6_1 | ~spl6_5)),
% 0.22/0.50    inference(superposition,[],[f19,f85])).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_funct_1(sK3,sK5(X0,X1,sK3)) = X0 | ~r2_hidden(X0,k9_relat_1(sK3,X1))) ) | (~spl6_1 | ~spl6_5)),
% 0.22/0.50    inference(resolution,[],[f70,f79])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK3) | k1_funct_1(sK3,X2) = X3) ) | (~spl6_1 | ~spl6_5)),
% 0.22/0.50    inference(subsumption_resolution,[],[f45,f66])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X2,X3] : (~v1_relat_1(sK3) | k1_funct_1(sK3,X2) = X3 | ~r2_hidden(k4_tarski(X2,X3),sK3)) ) | ~spl6_1),
% 0.22/0.50    inference(resolution,[],[f42,f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.50    inference(flattening,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    v1_funct_1(sK3) | ~spl6_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f40])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ( ! [X5] : (sK4 != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.22/0.50    inference(flattening,[],[f10])).
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.22/0.51    inference(negated_conjecture,[],[f8])).
% 0.22/0.51  fof(f8,conjecture,(
% 0.22/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    spl6_6 | ~spl6_3 | ~spl6_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f69,f58,f53,f74])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    spl6_4 <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (~spl6_3 | ~spl6_4)),
% 0.22/0.51    inference(subsumption_resolution,[],[f68,f55])).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_4),
% 0.22/0.51    inference(superposition,[],[f60,f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) | ~spl6_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f58])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    spl6_5 | ~spl6_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f62,f53,f64])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    v1_relat_1(sK3) | ~spl6_3),
% 0.22/0.51    inference(resolution,[],[f55,f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    spl6_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f20,f58])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    spl6_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f23,f53])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    spl6_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f21,f40])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    v1_funct_1(sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (17127)------------------------------
% 0.22/0.51  % (17127)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (17127)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (17127)Memory used [KB]: 10746
% 0.22/0.51  % (17127)Time elapsed: 0.060 s
% 0.22/0.51  % (17127)------------------------------
% 0.22/0.51  % (17127)------------------------------
% 0.22/0.51  % (17123)Success in time 0.132 s
%------------------------------------------------------------------------------
