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
% DateTime   : Thu Dec  3 13:06:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 206 expanded)
%              Number of leaves         :   12 (  45 expanded)
%              Depth                    :   15
%              Number of atoms          :  192 (1262 expanded)
%              Number of equality atoms :   26 ( 247 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f208,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f106,f174,f207])).

fof(f207,plain,(
    ~ spl8_1 ),
    inference(avatar_contradiction_clause,[],[f204])).

fof(f204,plain,
    ( $false
    | ~ spl8_1 ),
    inference(unit_resulting_resolution,[],[f57,f201])).

fof(f201,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl8_1 ),
    inference(backward_demodulation,[],[f128,f101])).

fof(f101,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl8_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f128,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(unit_resulting_resolution,[],[f28,f124,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

fof(f124,plain,(
    ~ v1_partfun1(sK3,sK0) ),
    inference(unit_resulting_resolution,[],[f26,f31,f29,f30,f28,f32,f63])).

fof(f63,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X5,X0)
      | ~ r1_partfun1(X2,X5)
      | r2_hidden(X5,k5_partfun1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X5,X0)
      | ~ r1_partfun1(X2,X5)
      | r2_hidden(X5,X3)
      | k5_partfun1(X0,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X4 != X5
      | ~ v1_partfun1(X5,X0)
      | ~ r1_partfun1(X2,X5)
      | r2_hidden(X4,X3)
      | k5_partfun1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_partfun1)).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( r1_partfun1(X2,X3)
             => ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
                | ( k1_xboole_0 != X0
                  & k1_xboole_0 = X1 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r1_partfun1(X2,X3)
           => ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
              | ( k1_xboole_0 != X0
                & k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_2)).

fof(f30,plain,(
    ~ r2_hidden(sK3,k5_partfun1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f29,plain,(
    r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f31,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f26,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f28,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f57,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f174,plain,(
    spl8_2 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f73,f168,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f168,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f129,f154,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f154,plain,
    ( r2_hidden(sK4(sK1,k1_xboole_0),sK1)
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f145,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f145,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f105,f136,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f136,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f134,f36])).

fof(f134,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f56,f129,f33])).

fof(f56,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f105,plain,
    ( k1_xboole_0 != sK1
    | spl8_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl8_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f129,plain,(
    v1_xboole_0(sK1) ),
    inference(unit_resulting_resolution,[],[f26,f27,f28,f124,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f27,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f73,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f106,plain,
    ( spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f25,f103,f99])).

fof(f25,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:39:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (18340)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.52  % (18332)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (18348)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.53  % (18339)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.53  % (18333)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (18321)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (18324)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (18323)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (18326)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (18328)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (18343)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (18331)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (18335)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (18325)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.55  % (18322)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.55  % (18320)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.55  % (18337)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (18337)Refutation not found, incomplete strategy% (18337)------------------------------
% 0.22/0.55  % (18337)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (18337)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (18337)Memory used [KB]: 10746
% 0.22/0.55  % (18337)Time elapsed: 0.135 s
% 0.22/0.55  % (18337)------------------------------
% 0.22/0.55  % (18337)------------------------------
% 0.22/0.55  % (18336)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (18327)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.55  % (18329)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (18338)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (18349)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.56  % (18344)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.56  % (18324)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % (18345)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.56  % (18341)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.56  % (18347)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.56  % (18330)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f208,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(avatar_sat_refutation,[],[f106,f174,f207])).
% 0.22/0.56  fof(f207,plain,(
% 0.22/0.56    ~spl8_1),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f204])).
% 0.22/0.56  fof(f204,plain,(
% 0.22/0.56    $false | ~spl8_1),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f57,f201])).
% 0.22/0.56  fof(f201,plain,(
% 0.22/0.56    ~v1_xboole_0(k1_xboole_0) | ~spl8_1),
% 0.22/0.56    inference(backward_demodulation,[],[f128,f101])).
% 0.22/0.56  fof(f101,plain,(
% 0.22/0.56    k1_xboole_0 = sK0 | ~spl8_1),
% 0.22/0.56    inference(avatar_component_clause,[],[f99])).
% 0.22/0.56  fof(f99,plain,(
% 0.22/0.56    spl8_1 <=> k1_xboole_0 = sK0),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.22/0.56  fof(f128,plain,(
% 0.22/0.56    ~v1_xboole_0(sK0)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f28,f124,f59])).
% 0.22/0.56  fof(f59,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f24])).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f9])).
% 0.22/0.56  fof(f9,axiom,(
% 0.22/0.56    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).
% 0.22/0.56  fof(f124,plain,(
% 0.22/0.56    ~v1_partfun1(sK3,sK0)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f26,f31,f29,f30,f28,f32,f63])).
% 0.22/0.56  fof(f63,plain,(
% 0.22/0.56    ( ! [X2,X0,X5,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(X5,X0) | ~r1_partfun1(X2,X5) | r2_hidden(X5,k5_partfun1(X0,X1,X2))) )),
% 0.22/0.56    inference(equality_resolution,[],[f62])).
% 0.22/0.56  fof(f62,plain,(
% 0.22/0.56    ( ! [X2,X0,X5,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(X5,X0) | ~r1_partfun1(X2,X5) | r2_hidden(X5,X3) | k5_partfun1(X0,X1,X2) != X3) )),
% 0.22/0.56    inference(equality_resolution,[],[f49])).
% 0.22/0.56  fof(f49,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X4 != X5 | ~v1_partfun1(X5,X0) | ~r1_partfun1(X2,X5) | r2_hidden(X4,X3) | k5_partfun1(X0,X1,X2) != X3) )),
% 0.22/0.56    inference(cnf_transformation,[],[f21])).
% 0.22/0.56  fof(f21,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.56    inference(flattening,[],[f20])).
% 0.22/0.56  fof(f20,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.56    inference(ennf_transformation,[],[f11])).
% 0.22/0.56  fof(f11,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_partfun1)).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.56    inference(cnf_transformation,[],[f15])).
% 0.22/0.56  fof(f15,plain,(
% 0.22/0.56    ? [X0,X1,X2] : (? [X3] : (~r2_hidden(X3,k5_partfun1(X0,X1,X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.22/0.56    inference(flattening,[],[f14])).
% 0.22/0.56  fof(f14,plain,(
% 0.22/0.56    ? [X0,X1,X2] : (? [X3] : (((~r2_hidden(X3,k5_partfun1(X0,X1,X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_partfun1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 0.22/0.56    inference(ennf_transformation,[],[f13])).
% 0.22/0.56  fof(f13,negated_conjecture,(
% 0.22/0.56    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.22/0.56    inference(negated_conjecture,[],[f12])).
% 0.22/0.56  fof(f12,conjecture,(
% 0.22/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_2)).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    ~r2_hidden(sK3,k5_partfun1(sK0,sK1,sK2))),
% 0.22/0.56    inference(cnf_transformation,[],[f15])).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    r1_partfun1(sK2,sK3)),
% 0.22/0.56    inference(cnf_transformation,[],[f15])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    v1_funct_1(sK2)),
% 0.22/0.56    inference(cnf_transformation,[],[f15])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    v1_funct_1(sK3)),
% 0.22/0.56    inference(cnf_transformation,[],[f15])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.56    inference(cnf_transformation,[],[f15])).
% 0.22/0.56  fof(f57,plain,(
% 0.22/0.56    v1_xboole_0(k1_xboole_0)),
% 0.22/0.56    inference(cnf_transformation,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    v1_xboole_0(k1_xboole_0)),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.56  fof(f174,plain,(
% 0.22/0.56    spl8_2),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f171])).
% 0.22/0.56  fof(f171,plain,(
% 0.22/0.56    $false | spl8_2),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f73,f168,f60])).
% 0.22/0.56  fof(f60,plain,(
% 0.22/0.56    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f6])).
% 0.22/0.56  fof(f6,axiom,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.56  fof(f168,plain,(
% 0.22/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | spl8_2),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f129,f154,f33])).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f16])).
% 0.22/0.56  fof(f16,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.22/0.56  fof(f154,plain,(
% 0.22/0.56    r2_hidden(sK4(sK1,k1_xboole_0),sK1) | spl8_2),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f145,f36])).
% 0.22/0.56  fof(f36,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f19])).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f1])).
% 0.22/0.56  fof(f1,axiom,(
% 0.22/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.56  fof(f145,plain,(
% 0.22/0.56    ~r1_tarski(sK1,k1_xboole_0) | spl8_2),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f105,f136,f55])).
% 0.22/0.56  fof(f55,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.56  fof(f136,plain,(
% 0.22/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f134,f36])).
% 0.22/0.56  fof(f134,plain,(
% 0.22/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f56,f129,f33])).
% 0.22/0.56  fof(f56,plain,(
% 0.22/0.56    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f5])).
% 0.22/0.56  fof(f5,axiom,(
% 0.22/0.56    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.56  fof(f105,plain,(
% 0.22/0.56    k1_xboole_0 != sK1 | spl8_2),
% 0.22/0.56    inference(avatar_component_clause,[],[f103])).
% 0.22/0.56  fof(f103,plain,(
% 0.22/0.56    spl8_2 <=> k1_xboole_0 = sK1),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.22/0.56  fof(f129,plain,(
% 0.22/0.56    v1_xboole_0(sK1)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f26,f27,f28,f124,f58])).
% 0.22/0.56  fof(f58,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f23])).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.56    inference(flattening,[],[f22])).
% 0.22/0.56  fof(f22,plain,(
% 0.22/0.56    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f10])).
% 0.22/0.56  fof(f10,axiom,(
% 0.22/0.56    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.22/0.56  fof(f27,plain,(
% 0.22/0.56    v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f15])).
% 0.22/0.56  fof(f73,plain,(
% 0.22/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.56    inference(equality_resolution,[],[f53])).
% 0.22/0.56  fof(f53,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f3])).
% 0.22/0.56  fof(f106,plain,(
% 0.22/0.56    spl8_1 | ~spl8_2),
% 0.22/0.56    inference(avatar_split_clause,[],[f25,f103,f99])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 0.22/0.56    inference(cnf_transformation,[],[f15])).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (18324)------------------------------
% 0.22/0.56  % (18324)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (18324)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (18324)Memory used [KB]: 6396
% 0.22/0.56  % (18324)Time elapsed: 0.129 s
% 0.22/0.56  % (18324)------------------------------
% 0.22/0.56  % (18324)------------------------------
% 0.22/0.56  % (18319)Success in time 0.198 s
%------------------------------------------------------------------------------
