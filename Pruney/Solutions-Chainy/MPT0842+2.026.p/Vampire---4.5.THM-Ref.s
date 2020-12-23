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
% DateTime   : Thu Dec  3 12:58:00 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 140 expanded)
%              Number of leaves         :   13 (  39 expanded)
%              Depth                    :   14
%              Number of atoms          :  206 ( 552 expanded)
%              Number of equality atoms :    5 (   8 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f136,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f57,f66,f83,f135])).

fof(f135,plain,
    ( ~ spl10_1
    | ~ spl10_5 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f133,f70])).

fof(f70,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f69,f27])).

fof(f27,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f69,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK2))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f22,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f22,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
                      <~> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X4,X5),X3)
                            & m1_subset_1(X5,X2) ) )
                      & m1_subset_1(X4,X0) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ~ v1_xboole_0(X2)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                   => ! [X4] :
                        ( m1_subset_1(X4,X0)
                       => ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
                        <=> ? [X5] :
                              ( r2_hidden(X5,X1)
                              & r2_hidden(k4_tarski(X4,X5),X3)
                              & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                 => ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X4,X5),X3)
                            & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_relset_1)).

fof(f133,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl10_1
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f132,f86])).

fof(f86,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f85,f22])).

fof(f85,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl10_1 ),
    inference(superposition,[],[f47,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f47,plain,
    ( r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl10_1
  <=> r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f132,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ v1_relat_1(sK3)
    | ~ spl10_5 ),
    inference(duplicate_literal_removal,[],[f131])).

fof(f131,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ v1_relat_1(sK3)
    | ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ spl10_5 ),
    inference(resolution,[],[f128,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X2),X1)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(f128,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK9(sK4,X0,sK3),sK1)
        | ~ r2_hidden(sK4,k10_relat_1(sK3,X0)) )
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f127,f96])).

fof(f96,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK9(X2,X3,sK3),sK2)
      | ~ r2_hidden(X2,k10_relat_1(sK3,X3)) ) ),
    inference(subsumption_resolution,[],[f95,f70])).

fof(f95,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK9(X2,X3,sK3),sK2)
      | ~ v1_relat_1(sK3)
      | ~ r2_hidden(X2,k10_relat_1(sK3,X3)) ) ),
    inference(resolution,[],[f77,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,sK9(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f77,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),sK3)
      | r2_hidden(X3,sK2) ) ),
    inference(resolution,[],[f68,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f68,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_zfmisc_1(sK0,sK2))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f22,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f127,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK9(sK4,X0,sK3),sK1)
        | ~ r2_hidden(sK4,k10_relat_1(sK3,X0))
        | ~ r2_hidden(sK9(sK4,X0,sK3),sK2) )
    | ~ spl10_5 ),
    inference(resolution,[],[f102,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f102,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK9(sK4,X0,sK3),sK2)
        | ~ r2_hidden(sK9(sK4,X0,sK3),sK1)
        | ~ r2_hidden(sK4,k10_relat_1(sK3,X0)) )
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f98,f70])).

fof(f98,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK9(sK4,X0,sK3),sK1)
        | ~ m1_subset_1(sK9(sK4,X0,sK3),sK2)
        | ~ v1_relat_1(sK3)
        | ~ r2_hidden(sK4,k10_relat_1(sK3,X0)) )
    | ~ spl10_5 ),
    inference(resolution,[],[f65,f35])).

fof(f65,plain,
    ( ! [X5] :
        ( ~ r2_hidden(k4_tarski(sK4,X5),sK3)
        | ~ r2_hidden(X5,sK1)
        | ~ m1_subset_1(X5,sK2) )
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl10_5
  <=> ! [X5] :
        ( ~ m1_subset_1(X5,sK2)
        | ~ r2_hidden(X5,sK1)
        | ~ r2_hidden(k4_tarski(sK4,X5),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f83,plain,
    ( spl10_1
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(avatar_contradiction_clause,[],[f82])).

fof(f82,plain,
    ( $false
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f80,f51])).

fof(f51,plain,
    ( r2_hidden(sK5,sK1)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl10_2
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f80,plain,
    ( ~ r2_hidden(sK5,sK1)
    | spl10_1
    | ~ spl10_3 ),
    inference(resolution,[],[f75,f56])).

fof(f56,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),sK3)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl10_3
  <=> r2_hidden(k4_tarski(sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f75,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK4,X0),sK3)
        | ~ r2_hidden(X0,sK1) )
    | spl10_1 ),
    inference(subsumption_resolution,[],[f74,f43])).

fof(f43,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f74,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | ~ r2_hidden(k4_tarski(sK4,X0),sK3)
        | ~ r2_hidden(X0,sK1) )
    | spl10_1 ),
    inference(subsumption_resolution,[],[f73,f70])).

fof(f73,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | ~ r2_hidden(k4_tarski(sK4,X0),sK3)
        | ~ r2_hidden(X0,sK1)
        | ~ v1_relat_1(sK3) )
    | spl10_1 ),
    inference(resolution,[],[f72,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f72,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | spl10_1 ),
    inference(subsumption_resolution,[],[f71,f22])).

fof(f71,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl10_1 ),
    inference(superposition,[],[f46,f38])).

fof(f46,plain,
    ( ~ r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))
    | spl10_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f66,plain,
    ( ~ spl10_1
    | spl10_5 ),
    inference(avatar_split_clause,[],[f17,f64,f45])).

fof(f17,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,sK2)
      | ~ r2_hidden(k4_tarski(sK4,X5),sK3)
      | ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f57,plain,
    ( spl10_1
    | spl10_3 ),
    inference(avatar_split_clause,[],[f19,f54,f45])).

fof(f19,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),sK3)
    | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f52,plain,
    ( spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f20,f49,f45])).

fof(f20,plain,
    ( r2_hidden(sK5,sK1)
    | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:15:09 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (9791)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (9792)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.51  % (9809)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.52  % (9791)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f136,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f52,f57,f66,f83,f135])).
% 0.20/0.52  fof(f135,plain,(
% 0.20/0.52    ~spl10_1 | ~spl10_5),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f134])).
% 0.20/0.52  fof(f134,plain,(
% 0.20/0.52    $false | (~spl10_1 | ~spl10_5)),
% 0.20/0.52    inference(subsumption_resolution,[],[f133,f70])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    v1_relat_1(sK3)),
% 0.20/0.52    inference(subsumption_resolution,[],[f69,f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    ~v1_relat_1(k2_zfmisc_1(sK0,sK2)) | v1_relat_1(sK3)),
% 0.20/0.52    inference(resolution,[],[f22,f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <~> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,negated_conjecture,(
% 0.20/0.52    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))))))))),
% 0.20/0.52    inference(negated_conjecture,[],[f9])).
% 0.20/0.52  fof(f9,conjecture,(
% 0.20/0.52    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))))))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_relset_1)).
% 0.20/0.52  fof(f133,plain,(
% 0.20/0.52    ~v1_relat_1(sK3) | (~spl10_1 | ~spl10_5)),
% 0.20/0.52    inference(subsumption_resolution,[],[f132,f86])).
% 0.20/0.52  fof(f86,plain,(
% 0.20/0.52    r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~spl10_1),
% 0.20/0.52    inference(subsumption_resolution,[],[f85,f22])).
% 0.20/0.52  fof(f85,plain,(
% 0.20/0.52    r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl10_1),
% 0.20/0.52    inference(superposition,[],[f47,f38])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) | ~spl10_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f45])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    spl10_1 <=> r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.20/0.52  fof(f132,plain,(
% 0.20/0.52    ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~v1_relat_1(sK3) | ~spl10_5),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f131])).
% 0.20/0.52  fof(f131,plain,(
% 0.20/0.52    ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~v1_relat_1(sK3) | ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~spl10_5),
% 0.20/0.52    inference(resolution,[],[f128,f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r2_hidden(sK9(X0,X1,X2),X1) | ~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).
% 0.20/0.52  fof(f128,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(sK9(sK4,X0,sK3),sK1) | ~r2_hidden(sK4,k10_relat_1(sK3,X0))) ) | ~spl10_5),
% 0.20/0.52    inference(subsumption_resolution,[],[f127,f96])).
% 0.20/0.52  fof(f96,plain,(
% 0.20/0.52    ( ! [X2,X3] : (r2_hidden(sK9(X2,X3,sK3),sK2) | ~r2_hidden(X2,k10_relat_1(sK3,X3))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f95,f70])).
% 0.20/0.52  fof(f95,plain,(
% 0.20/0.52    ( ! [X2,X3] : (r2_hidden(sK9(X2,X3,sK3),sK2) | ~v1_relat_1(sK3) | ~r2_hidden(X2,k10_relat_1(sK3,X3))) )),
% 0.20/0.52    inference(resolution,[],[f77,f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,sK9(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f77,plain,(
% 0.20/0.52    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK3) | r2_hidden(X3,sK2)) )),
% 0.20/0.52    inference(resolution,[],[f68,f40])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(sK0,sK2)) | ~r2_hidden(X0,sK3)) )),
% 0.20/0.52    inference(resolution,[],[f22,f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.52  fof(f127,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(sK9(sK4,X0,sK3),sK1) | ~r2_hidden(sK4,k10_relat_1(sK3,X0)) | ~r2_hidden(sK9(sK4,X0,sK3),sK2)) ) | ~spl10_5),
% 0.20/0.52    inference(resolution,[],[f102,f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.20/0.52  fof(f102,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(sK9(sK4,X0,sK3),sK2) | ~r2_hidden(sK9(sK4,X0,sK3),sK1) | ~r2_hidden(sK4,k10_relat_1(sK3,X0))) ) | ~spl10_5),
% 0.20/0.52    inference(subsumption_resolution,[],[f98,f70])).
% 0.20/0.52  fof(f98,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(sK9(sK4,X0,sK3),sK1) | ~m1_subset_1(sK9(sK4,X0,sK3),sK2) | ~v1_relat_1(sK3) | ~r2_hidden(sK4,k10_relat_1(sK3,X0))) ) | ~spl10_5),
% 0.20/0.52    inference(resolution,[],[f65,f35])).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    ( ! [X5] : (~r2_hidden(k4_tarski(sK4,X5),sK3) | ~r2_hidden(X5,sK1) | ~m1_subset_1(X5,sK2)) ) | ~spl10_5),
% 0.20/0.52    inference(avatar_component_clause,[],[f64])).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    spl10_5 <=> ! [X5] : (~m1_subset_1(X5,sK2) | ~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(sK4,X5),sK3))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.20/0.52  fof(f83,plain,(
% 0.20/0.52    spl10_1 | ~spl10_2 | ~spl10_3),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f82])).
% 0.20/0.52  fof(f82,plain,(
% 0.20/0.52    $false | (spl10_1 | ~spl10_2 | ~spl10_3)),
% 0.20/0.52    inference(subsumption_resolution,[],[f80,f51])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    r2_hidden(sK5,sK1) | ~spl10_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f49])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    spl10_2 <=> r2_hidden(sK5,sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.20/0.52  fof(f80,plain,(
% 0.20/0.52    ~r2_hidden(sK5,sK1) | (spl10_1 | ~spl10_3)),
% 0.20/0.52    inference(resolution,[],[f75,f56])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    r2_hidden(k4_tarski(sK4,sK5),sK3) | ~spl10_3),
% 0.20/0.52    inference(avatar_component_clause,[],[f54])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    spl10_3 <=> r2_hidden(k4_tarski(sK4,sK5),sK3)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.20/0.52  fof(f75,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(k4_tarski(sK4,X0),sK3) | ~r2_hidden(X0,sK1)) ) | spl10_1),
% 0.20/0.52    inference(subsumption_resolution,[],[f74,f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,k2_relat_1(X0))) )),
% 0.20/0.52    inference(equality_resolution,[],[f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 0.20/0.52  fof(f74,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | ~r2_hidden(k4_tarski(sK4,X0),sK3) | ~r2_hidden(X0,sK1)) ) | spl10_1),
% 0.20/0.52    inference(subsumption_resolution,[],[f73,f70])).
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | ~r2_hidden(k4_tarski(sK4,X0),sK3) | ~r2_hidden(X0,sK1) | ~v1_relat_1(sK3)) ) | spl10_1),
% 0.20/0.52    inference(resolution,[],[f72,f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k10_relat_1(X2,X1)) | ~r2_hidden(X3,k2_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,X1) | ~v1_relat_1(X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f72,plain,(
% 0.20/0.52    ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | spl10_1),
% 0.20/0.52    inference(subsumption_resolution,[],[f71,f22])).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl10_1),
% 0.20/0.52    inference(superposition,[],[f46,f38])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ~r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) | spl10_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f45])).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    ~spl10_1 | spl10_5),
% 0.20/0.52    inference(avatar_split_clause,[],[f17,f64,f45])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ( ! [X5] : (~m1_subset_1(X5,sK2) | ~r2_hidden(k4_tarski(sK4,X5),sK3) | ~r2_hidden(X5,sK1) | ~r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    spl10_1 | spl10_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f19,f54,f45])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    r2_hidden(k4_tarski(sK4,sK5),sK3) | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    spl10_1 | spl10_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f20,f49,f45])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    r2_hidden(sK5,sK1) | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (9791)------------------------------
% 0.20/0.52  % (9791)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (9791)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (9791)Memory used [KB]: 10618
% 0.20/0.52  % (9791)Time elapsed: 0.084 s
% 0.20/0.52  % (9791)------------------------------
% 0.20/0.52  % (9791)------------------------------
% 0.20/0.52  % (9789)Success in time 0.164 s
%------------------------------------------------------------------------------
