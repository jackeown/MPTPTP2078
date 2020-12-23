%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 210 expanded)
%              Number of leaves         :   14 (  72 expanded)
%              Depth                    :   12
%              Number of atoms          :  232 (1211 expanded)
%              Number of equality atoms :   14 ( 140 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f124,plain,(
    $false ),
    inference(resolution,[],[f120,f60])).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f120,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f118,f109])).

fof(f109,plain,(
    k1_xboole_0 = k1_funct_1(sK5,sK6(sK5)) ),
    inference(unit_resulting_resolution,[],[f86,f53])).

fof(f53,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f86,plain,(
    v1_xboole_0(k1_funct_1(sK5,sK6(sK5))) ),
    inference(unit_resulting_resolution,[],[f79,f51])).

fof(f51,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_funct_1(X0,sK6(X0)))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( v1_xboole_0(k1_funct_1(X0,sK6(X0)))
          & r2_hidden(sK6(X0),k1_relat_1(X0)) ) )
      & ( ! [X2] :
            ( ~ v1_xboole_0(k1_funct_1(X0,X2))
            | ~ r2_hidden(X2,k1_relat_1(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f31,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(k1_funct_1(X0,X1))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( v1_xboole_0(k1_funct_1(X0,sK6(X0)))
        & r2_hidden(sK6(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( v1_xboole_0(k1_funct_1(X0,X1))
            & r2_hidden(X1,k1_relat_1(X0)) ) )
      & ( ! [X2] :
            ( ~ v1_xboole_0(k1_funct_1(X0,X2))
            | ~ r2_hidden(X2,k1_relat_1(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( v1_xboole_0(k1_funct_1(X0,X1))
            & r2_hidden(X1,k1_relat_1(X0)) ) )
      & ( ! [X1] :
            ( ~ v1_xboole_0(k1_funct_1(X0,X1))
            | ~ r2_hidden(X1,k1_relat_1(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1] :
          ( ~ v1_xboole_0(k1_funct_1(X0,X1))
          | ~ r2_hidden(X1,k1_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f79,plain,(
    ~ sP0(sK5) ),
    inference(unit_resulting_resolution,[],[f46,f72,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ sP0(X0)
      | v2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( ( v2_relat_1(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v2_relat_1(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v2_relat_1(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f72,plain,(
    sP1(sK5) ),
    inference(unit_resulting_resolution,[],[f42,f43,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f13,f21,f20])).

fof(f13,plain,(
    ! [X0] :
      ( ( v2_relat_1(X0)
      <=> ! [X1] :
            ( ~ v1_xboole_0(k1_funct_1(X0,X1))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v2_relat_1(X0)
      <=> ! [X1] :
            ( ~ v1_xboole_0(k1_funct_1(X0,X1))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_relat_1(X0)
      <=> ! [X1] :
            ~ ( v1_xboole_0(k1_funct_1(X0,X1))
              & r2_hidden(X1,k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_funct_1)).

fof(f43,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ v2_relat_1(sK5)
    & k1_relat_1(sK4) = k1_relat_1(sK5)
    & v5_funct_1(sK4,sK5)
    & v1_funct_1(sK5)
    & v1_relat_1(sK5)
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f11,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_relat_1(X1)
            & k1_relat_1(X0) = k1_relat_1(X1)
            & v5_funct_1(X0,X1)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ v2_relat_1(X1)
          & k1_relat_1(X1) = k1_relat_1(sK4)
          & v5_funct_1(sK4,X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ~ v2_relat_1(X1)
        & k1_relat_1(X1) = k1_relat_1(sK4)
        & v5_funct_1(sK4,X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ v2_relat_1(sK5)
      & k1_relat_1(sK4) = k1_relat_1(sK5)
      & v5_funct_1(sK4,sK5)
      & v1_funct_1(sK5)
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_relat_1(X1)
          & k1_relat_1(X0) = k1_relat_1(X1)
          & v5_funct_1(X0,X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_relat_1(X1)
          & k1_relat_1(X0) = k1_relat_1(X1)
          & v5_funct_1(X0,X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k1_relat_1(X0) = k1_relat_1(X1)
                & v5_funct_1(X0,X1) )
             => v2_relat_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k1_relat_1(X0) = k1_relat_1(X1)
              & v5_funct_1(X0,X1) )
           => v2_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_funct_1)).

fof(f42,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f46,plain,(
    ~ v2_relat_1(sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f118,plain,(
    ~ m1_subset_1(k1_funct_1(sK5,sK6(sK5)),k1_zfmisc_1(k1_funct_1(sK5,sK6(sK5)))) ),
    inference(unit_resulting_resolution,[],[f86,f97,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f97,plain,(
    r2_hidden(k1_funct_1(sK4,sK6(sK5)),k1_funct_1(sK5,sK6(sK5))) ),
    inference(unit_resulting_resolution,[],[f89,f82,f56])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
      | ~ r2_hidden(X3,k1_relat_1(X1))
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ( ~ r2_hidden(k1_funct_1(X1,sK7(X0,X1)),k1_funct_1(X0,sK7(X0,X1)))
          & r2_hidden(sK7(X0,X1),k1_relat_1(X1)) ) )
      & ( ! [X3] :
            ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
            | ~ r2_hidden(X3,k1_relat_1(X1)) )
        | ~ sP2(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f37,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
          & r2_hidden(X2,k1_relat_1(X1)) )
     => ( ~ r2_hidden(k1_funct_1(X1,sK7(X0,X1)),k1_funct_1(X0,sK7(X0,X1)))
        & r2_hidden(sK7(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
            & r2_hidden(X2,k1_relat_1(X1)) ) )
      & ( ! [X3] :
            ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
            | ~ r2_hidden(X3,k1_relat_1(X1)) )
        | ~ sP2(X0,X1) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
            & r2_hidden(X2,k1_relat_1(X1)) ) )
      & ( ! [X2] :
            ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
            | ~ r2_hidden(X2,k1_relat_1(X1)) )
        | ~ sP2(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
          | ~ r2_hidden(X2,k1_relat_1(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f82,plain,(
    r2_hidden(sK6(sK5),k1_relat_1(sK4)) ),
    inference(subsumption_resolution,[],[f78,f79])).

fof(f78,plain,
    ( r2_hidden(sK6(sK5),k1_relat_1(sK4))
    | sP0(sK5) ),
    inference(superposition,[],[f50,f45])).

fof(f45,plain,(
    k1_relat_1(sK4) = k1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f50,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),k1_relat_1(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f89,plain,(
    sP2(sK5,sK4) ),
    inference(unit_resulting_resolution,[],[f44,f68,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ sP3(X0,X1)
      | ~ v5_funct_1(X0,X1)
      | sP2(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( v5_funct_1(X0,X1)
          | ~ sP2(X1,X0) )
        & ( sP2(X1,X0)
          | ~ v5_funct_1(X0,X1) ) )
      | ~ sP3(X0,X1) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ( ( v5_funct_1(X1,X0)
          | ~ sP2(X0,X1) )
        & ( sP2(X0,X1)
          | ~ v5_funct_1(X1,X0) ) )
      | ~ sP3(X1,X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ( v5_funct_1(X1,X0)
      <=> sP2(X0,X1) )
      | ~ sP3(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f68,plain,(
    sP3(sK4,sK5) ),
    inference(unit_resulting_resolution,[],[f40,f41,f42,f43,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( sP3(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP3(X1,X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f16,f24,f23])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,k1_relat_1(X1))
               => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).

fof(f41,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f40,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f44,plain,(
    v5_funct_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:16:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (26695)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.50  % (26695)Refutation not found, incomplete strategy% (26695)------------------------------
% 0.22/0.50  % (26695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (26703)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.51  % (26695)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (26695)Memory used [KB]: 10618
% 0.22/0.51  % (26695)Time elapsed: 0.062 s
% 0.22/0.51  % (26695)------------------------------
% 0.22/0.51  % (26695)------------------------------
% 0.22/0.51  % (26703)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f124,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(resolution,[],[f120,f60])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.51  fof(f120,plain,(
% 0.22/0.51    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.51    inference(forward_demodulation,[],[f118,f109])).
% 0.22/0.51  fof(f109,plain,(
% 0.22/0.51    k1_xboole_0 = k1_funct_1(sK5,sK6(sK5))),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f86,f53])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    v1_xboole_0(k1_funct_1(sK5,sK6(sK5)))),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f79,f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    ( ! [X0] : (v1_xboole_0(k1_funct_1(X0,sK6(X0))) | sP0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ! [X0] : ((sP0(X0) | (v1_xboole_0(k1_funct_1(X0,sK6(X0))) & r2_hidden(sK6(X0),k1_relat_1(X0)))) & (! [X2] : (~v1_xboole_0(k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X0))) | ~sP0(X0)))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f31,f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ! [X0] : (? [X1] : (v1_xboole_0(k1_funct_1(X0,X1)) & r2_hidden(X1,k1_relat_1(X0))) => (v1_xboole_0(k1_funct_1(X0,sK6(X0))) & r2_hidden(sK6(X0),k1_relat_1(X0))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ! [X0] : ((sP0(X0) | ? [X1] : (v1_xboole_0(k1_funct_1(X0,X1)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X2] : (~v1_xboole_0(k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X0))) | ~sP0(X0)))),
% 0.22/0.51    inference(rectify,[],[f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ! [X0] : ((sP0(X0) | ? [X1] : (v1_xboole_0(k1_funct_1(X0,X1)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1] : (~v1_xboole_0(k1_funct_1(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~sP0(X0)))),
% 0.22/0.51    inference(nnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0] : (sP0(X0) <=> ! [X1] : (~v1_xboole_0(k1_funct_1(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X0))))),
% 0.22/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    ~sP0(sK5)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f46,f72,f48])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ( ! [X0] : (~sP1(X0) | ~sP0(X0) | v2_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X0] : (((v2_relat_1(X0) | ~sP0(X0)) & (sP0(X0) | ~v2_relat_1(X0))) | ~sP1(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0] : ((v2_relat_1(X0) <=> sP0(X0)) | ~sP1(X0))),
% 0.22/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    sP1(sK5)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f42,f43,f52])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_funct_1(X0) | sP1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(definition_folding,[],[f13,f21,f20])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X0] : ((v2_relat_1(X0) <=> ! [X1] : (~v1_xboole_0(k1_funct_1(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ! [X0] : ((v2_relat_1(X0) <=> ! [X1] : (~v1_xboole_0(k1_funct_1(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_relat_1(X0) <=> ! [X1] : ~(v1_xboole_0(k1_funct_1(X0,X1)) & r2_hidden(X1,k1_relat_1(X0)))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_funct_1)).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    v1_funct_1(sK5)),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    (~v2_relat_1(sK5) & k1_relat_1(sK4) = k1_relat_1(sK5) & v5_funct_1(sK4,sK5) & v1_funct_1(sK5) & v1_relat_1(sK5)) & v1_funct_1(sK4) & v1_relat_1(sK4)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f11,f27,f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (~v2_relat_1(X1) & k1_relat_1(X0) = k1_relat_1(X1) & v5_funct_1(X0,X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (~v2_relat_1(X1) & k1_relat_1(X1) = k1_relat_1(sK4) & v5_funct_1(sK4,X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK4) & v1_relat_1(sK4))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ? [X1] : (~v2_relat_1(X1) & k1_relat_1(X1) = k1_relat_1(sK4) & v5_funct_1(sK4,X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (~v2_relat_1(sK5) & k1_relat_1(sK4) = k1_relat_1(sK5) & v5_funct_1(sK4,sK5) & v1_funct_1(sK5) & v1_relat_1(sK5))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (~v2_relat_1(X1) & k1_relat_1(X0) = k1_relat_1(X1) & v5_funct_1(X0,X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : ((~v2_relat_1(X1) & (k1_relat_1(X0) = k1_relat_1(X1) & v5_funct_1(X0,X1))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,negated_conjecture,(
% 0.22/0.51    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k1_relat_1(X1) & v5_funct_1(X0,X1)) => v2_relat_1(X1))))),
% 0.22/0.51    inference(negated_conjecture,[],[f8])).
% 0.22/0.51  fof(f8,conjecture,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k1_relat_1(X1) & v5_funct_1(X0,X1)) => v2_relat_1(X1))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_funct_1)).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    v1_relat_1(sK5)),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ~v2_relat_1(sK5)),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  fof(f118,plain,(
% 0.22/0.51    ~m1_subset_1(k1_funct_1(sK5,sK6(sK5)),k1_zfmisc_1(k1_funct_1(sK5,sK6(sK5))))),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f86,f97,f62])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.22/0.51  fof(f97,plain,(
% 0.22/0.51    r2_hidden(k1_funct_1(sK4,sK6(sK5)),k1_funct_1(sK5,sK6(sK5)))),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f89,f82,f56])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    ( ! [X0,X3,X1] : (r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3)) | ~r2_hidden(X3,k1_relat_1(X1)) | ~sP2(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ! [X0,X1] : ((sP2(X0,X1) | (~r2_hidden(k1_funct_1(X1,sK7(X0,X1)),k1_funct_1(X0,sK7(X0,X1))) & r2_hidden(sK7(X0,X1),k1_relat_1(X1)))) & (! [X3] : (r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3)) | ~r2_hidden(X3,k1_relat_1(X1))) | ~sP2(X0,X1)))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f37,f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ! [X1,X0] : (? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1))) => (~r2_hidden(k1_funct_1(X1,sK7(X0,X1)),k1_funct_1(X0,sK7(X0,X1))) & r2_hidden(sK7(X0,X1),k1_relat_1(X1))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ! [X0,X1] : ((sP2(X0,X1) | ? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1)))) & (! [X3] : (r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3)) | ~r2_hidden(X3,k1_relat_1(X1))) | ~sP2(X0,X1)))),
% 0.22/0.51    inference(rectify,[],[f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ! [X0,X1] : ((sP2(X0,X1) | ? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1)))) & (! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1))) | ~sP2(X0,X1)))),
% 0.22/0.51    inference(nnf_transformation,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0,X1] : (sP2(X0,X1) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1))))),
% 0.22/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.51  fof(f82,plain,(
% 0.22/0.51    r2_hidden(sK6(sK5),k1_relat_1(sK4))),
% 0.22/0.51    inference(subsumption_resolution,[],[f78,f79])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    r2_hidden(sK6(sK5),k1_relat_1(sK4)) | sP0(sK5)),
% 0.22/0.51    inference(superposition,[],[f50,f45])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    k1_relat_1(sK4) = k1_relat_1(sK5)),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    ( ! [X0] : (r2_hidden(sK6(X0),k1_relat_1(X0)) | sP0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f33])).
% 0.22/0.51  fof(f89,plain,(
% 0.22/0.51    sP2(sK5,sK4)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f44,f68,f54])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~sP3(X0,X1) | ~v5_funct_1(X0,X1) | sP2(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ! [X0,X1] : (((v5_funct_1(X0,X1) | ~sP2(X1,X0)) & (sP2(X1,X0) | ~v5_funct_1(X0,X1))) | ~sP3(X0,X1))),
% 0.22/0.51    inference(rectify,[],[f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ! [X1,X0] : (((v5_funct_1(X1,X0) | ~sP2(X0,X1)) & (sP2(X0,X1) | ~v5_funct_1(X1,X0))) | ~sP3(X1,X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X1,X0] : ((v5_funct_1(X1,X0) <=> sP2(X0,X1)) | ~sP3(X1,X0))),
% 0.22/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    sP3(sK4,sK5)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f40,f41,f42,f43,f59])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    ( ! [X0,X1] : (sP3(X1,X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (sP3(X1,X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(definition_folding,[],[f16,f24,f23])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    v1_funct_1(sK4)),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    v1_relat_1(sK4)),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    v5_funct_1(sK4,sK5)),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (26703)------------------------------
% 0.22/0.51  % (26703)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (26703)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (26703)Memory used [KB]: 1663
% 0.22/0.51  % (26703)Time elapsed: 0.076 s
% 0.22/0.51  % (26703)------------------------------
% 0.22/0.51  % (26703)------------------------------
% 0.22/0.51  % (26686)Success in time 0.146 s
%------------------------------------------------------------------------------
