%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 197 expanded)
%              Number of leaves         :   15 (  69 expanded)
%              Depth                    :   13
%              Number of atoms          :  177 ( 916 expanded)
%              Number of equality atoms :   35 ( 183 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f230,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f150,f229])).

fof(f229,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f228])).

fof(f228,plain,
    ( $false
    | spl4_2 ),
    inference(subsumption_resolution,[],[f225,f227])).

fof(f227,plain,
    ( ~ r2_hidden(sK3(sK1,k2_relat_1(sK2)),k2_relat_1(sK2))
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f226,f152])).

fof(f152,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_relat_1(sK2))
      | ~ m1_subset_1(X3,sK1) ) ),
    inference(forward_demodulation,[],[f34,f145])).

fof(f145,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f43,f32])).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,sK2))
        | ~ m1_subset_1(X3,sK1) )
    & k1_xboole_0 != k1_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f26,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                    | ~ m1_subset_1(X3,X1) )
                & k1_xboole_0 != k1_relset_1(X0,X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(sK0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(sK0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ! [X3] :
                ( ~ r2_hidden(X3,k2_relset_1(sK0,X1,X2))
                | ~ m1_subset_1(X3,X1) )
            & k1_xboole_0 != k1_relset_1(sK0,X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,X2))
              | ~ m1_subset_1(X3,sK1) )
          & k1_xboole_0 != k1_relset_1(sK0,sK1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X2] :
        ( ! [X3] :
            ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,X2))
            | ~ m1_subset_1(X3,sK1) )
        & k1_xboole_0 != k1_relset_1(sK0,sK1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
   => ( ! [X3] :
          ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,sK2))
          | ~ m1_subset_1(X3,sK1) )
      & k1_xboole_0 != k1_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(X0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(X0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,X1)
                       => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                    & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                  & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f34,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,sK2))
      | ~ m1_subset_1(X3,sK1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f226,plain,
    ( m1_subset_1(sK3(sK1,k2_relat_1(sK2)),sK1)
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f218,f222,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ~ ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

fof(f222,plain,(
    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(forward_demodulation,[],[f219,f145])).

fof(f219,plain,(
    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f32,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f218,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | spl4_2 ),
    inference(superposition,[],[f114,f145])).

fof(f114,plain,
    ( k1_xboole_0 != k2_relset_1(sK0,sK1,sK2)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl4_2
  <=> k1_xboole_0 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f225,plain,
    ( r2_hidden(sK3(sK1,k2_relat_1(sK2)),k2_relat_1(sK2))
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f218,f222,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f150,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f35,f148])).

fof(f148,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f140,f147])).

fof(f147,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f144,f115])).

fof(f115,plain,
    ( k1_xboole_0 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f113])).

fof(f144,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f32,f43])).

fof(f140,plain,(
    ~ v1_xboole_0(k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f65,f138,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

fof(f138,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(unit_resulting_resolution,[],[f137,f37])).

fof(f37,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

fof(f137,plain,(
    ~ v1_xboole_0(k1_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f56,f134])).

fof(f134,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f32,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f56,plain,(
    ~ v1_xboole_0(k1_relset_1(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f33,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f33,plain,(
    k1_xboole_0 != k1_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f65,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f32,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f35,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:10:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (10070)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.52  % (10070)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (10062)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.52  % (10069)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f230,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f150,f229])).
% 0.21/0.52  fof(f229,plain,(
% 0.21/0.52    spl4_2),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f228])).
% 0.21/0.52  fof(f228,plain,(
% 0.21/0.52    $false | spl4_2),
% 0.21/0.52    inference(subsumption_resolution,[],[f225,f227])).
% 0.21/0.52  fof(f227,plain,(
% 0.21/0.52    ~r2_hidden(sK3(sK1,k2_relat_1(sK2)),k2_relat_1(sK2)) | spl4_2),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f226,f152])).
% 0.21/0.52  fof(f152,plain,(
% 0.21/0.52    ( ! [X3] : (~r2_hidden(X3,k2_relat_1(sK2)) | ~m1_subset_1(X3,sK1)) )),
% 0.21/0.52    inference(forward_demodulation,[],[f34,f145])).
% 0.21/0.52  fof(f145,plain,(
% 0.21/0.52    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.21/0.52    inference(resolution,[],[f43,f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ((! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,sK2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k1_relset_1(sK0,sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f26,f25,f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(sK0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(sK0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))) & ~v1_xboole_0(X1)) => (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,X2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k1_relset_1(sK0,sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) & ~v1_xboole_0(sK1))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,X2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k1_relset_1(sK0,sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) => (! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,sK2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k1_relset_1(sK0,sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.52    inference(flattening,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,negated_conjecture,(
% 0.21/0.52    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 0.21/0.52    inference(negated_conjecture,[],[f10])).
% 0.21/0.52  fof(f10,conjecture,(
% 0.21/0.52    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,sK2)) | ~m1_subset_1(X3,sK1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f226,plain,(
% 0.21/0.52    m1_subset_1(sK3(sK1,k2_relat_1(sK2)),sK1) | spl4_2),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f218,f222,f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),X0) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0,X1] : ((r2_hidden(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (r2_hidden(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),X0)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0,X1] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(flattening,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0,X1] : ((? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).
% 0.21/0.53  fof(f222,plain,(
% 0.21/0.53    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.21/0.53    inference(forward_demodulation,[],[f219,f145])).
% 0.21/0.53  fof(f219,plain,(
% 0.21/0.53    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f32,f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.21/0.53  fof(f218,plain,(
% 0.21/0.53    k1_xboole_0 != k2_relat_1(sK2) | spl4_2),
% 0.21/0.53    inference(superposition,[],[f114,f145])).
% 0.21/0.53  fof(f114,plain,(
% 0.21/0.53    k1_xboole_0 != k2_relset_1(sK0,sK1,sK2) | spl4_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f113])).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    spl4_2 <=> k1_xboole_0 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.53  fof(f225,plain,(
% 0.21/0.53    r2_hidden(sK3(sK1,k2_relat_1(sK2)),k2_relat_1(sK2)) | spl4_2),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f218,f222,f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f150,plain,(
% 0.21/0.53    ~spl4_2),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f149])).
% 0.21/0.53  fof(f149,plain,(
% 0.21/0.53    $false | ~spl4_2),
% 0.21/0.53    inference(subsumption_resolution,[],[f35,f148])).
% 0.21/0.53  fof(f148,plain,(
% 0.21/0.53    ~v1_xboole_0(k1_xboole_0) | ~spl4_2),
% 0.21/0.53    inference(backward_demodulation,[],[f140,f147])).
% 0.21/0.53  fof(f147,plain,(
% 0.21/0.53    k1_xboole_0 = k2_relat_1(sK2) | ~spl4_2),
% 0.21/0.53    inference(forward_demodulation,[],[f144,f115])).
% 0.21/0.53  fof(f115,plain,(
% 0.21/0.53    k1_xboole_0 = k2_relset_1(sK0,sK1,sK2) | ~spl4_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f113])).
% 0.21/0.53  fof(f144,plain,(
% 0.21/0.53    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f32,f43])).
% 0.21/0.53  fof(f140,plain,(
% 0.21/0.53    ~v1_xboole_0(k2_relat_1(sK2))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f65,f138,f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.21/0.53    inference(flattening,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).
% 0.21/0.53  fof(f138,plain,(
% 0.21/0.53    ~v1_xboole_0(sK2)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f137,f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ( ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).
% 0.21/0.53  fof(f137,plain,(
% 0.21/0.53    ~v1_xboole_0(k1_relat_1(sK2))),
% 0.21/0.53    inference(backward_demodulation,[],[f56,f134])).
% 0.21/0.53  fof(f134,plain,(
% 0.21/0.53    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f32,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ~v1_xboole_0(k1_relset_1(sK0,sK1,sK2))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f33,f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    k1_xboole_0 != k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    v1_relat_1(sK2)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f32,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    v1_xboole_0(k1_xboole_0)),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    v1_xboole_0(k1_xboole_0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (10070)------------------------------
% 0.21/0.53  % (10070)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (10070)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (10070)Memory used [KB]: 10618
% 0.21/0.53  % (10070)Time elapsed: 0.084 s
% 0.21/0.53  % (10070)------------------------------
% 0.21/0.53  % (10070)------------------------------
% 0.21/0.53  % (10055)Success in time 0.168 s
%------------------------------------------------------------------------------
