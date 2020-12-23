%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0414+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:56 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   45 (  98 expanded)
%              Number of leaves         :    8 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :  111 ( 296 expanded)
%              Number of equality atoms :    8 (  25 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f208,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f179,f207])).

fof(f207,plain,(
    spl5_2 ),
    inference(avatar_contradiction_clause,[],[f198])).

fof(f198,plain,
    ( $false
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f185,f185,f186,f40,f78])).

fof(f78,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,k1_zfmisc_1(sK0))
      | r2_hidden(X1,sK2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f44,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f44,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X1,sK1)
      | r2_hidden(X1,sK2) ) ),
    inference(resolution,[],[f12,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f12,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(sK0))
      | r2_hidden(X3,sK2)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(X0))
                 => ( r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_setfam_1)).

fof(f40,plain,(
    r1_tarski(sK1,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f15,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f15,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f186,plain,
    ( ~ r2_hidden(sK3(sK1,sK2),sK2)
    | spl5_2 ),
    inference(resolution,[],[f60,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f60,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl5_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f185,plain,
    ( r2_hidden(sK3(sK1,sK2),sK1)
    | spl5_2 ),
    inference(resolution,[],[f60,f21])).

% (13159)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f179,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f64,f63,f63,f39,f76])).

fof(f76,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X1,sK2)
      | ~ r2_hidden(X1,X2)
      | r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f42,f20])).

fof(f42,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_zfmisc_1(sK0))
      | r2_hidden(X1,sK1)
      | ~ r2_hidden(X1,sK2) ) ),
    inference(resolution,[],[f11,f16])).

fof(f11,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X3,sK2)
      | r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f39,plain,(
    r1_tarski(sK2,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f13,f24])).

fof(f13,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f63,plain,
    ( r2_hidden(sK3(sK2,sK1),sK2)
    | spl5_1 ),
    inference(resolution,[],[f56,f21])).

fof(f56,plain,
    ( ~ r1_tarski(sK2,sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl5_1
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f64,plain,
    ( ~ r2_hidden(sK3(sK2,sK1),sK1)
    | spl5_1 ),
    inference(resolution,[],[f56,f22])).

fof(f61,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f33,f58,f54])).

fof(f33,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r1_tarski(sK2,sK1) ),
    inference(resolution,[],[f28,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | sQ4_eqProxy(X0,X1) ) ),
    inference(equality_proxy_replacement,[],[f19,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( sQ4_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f28,plain,(
    ~ sQ4_eqProxy(sK1,sK2) ),
    inference(equality_proxy_replacement,[],[f14,f27])).

fof(f14,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f8])).

%------------------------------------------------------------------------------
