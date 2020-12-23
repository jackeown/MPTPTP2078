%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 848 expanded)
%              Number of leaves         :   24 ( 295 expanded)
%              Depth                    :   16
%              Number of atoms          :  525 (7491 expanded)
%              Number of equality atoms :   88 (2321 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f446,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f130,f151,f318,f330,f335,f339,f349,f445])).

fof(f445,plain,
    ( spl9_2
    | ~ spl9_25 ),
    inference(avatar_contradiction_clause,[],[f440])).

fof(f440,plain,
    ( $false
    | spl9_2
    | ~ spl9_25 ),
    inference(resolution,[],[f438,f125])).

fof(f125,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl9_2
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f438,plain,
    ( ! [X0] : v1_funct_2(sK2,sK0,X0)
    | ~ spl9_25 ),
    inference(resolution,[],[f171,f338])).

fof(f338,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK0)
    | ~ spl9_25 ),
    inference(avatar_component_clause,[],[f337])).

fof(f337,plain,
    ( spl9_25
  <=> ! [X1] : ~ r2_hidden(X1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f171,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK0,X0,sK2),sK0)
      | v1_funct_2(sK2,sK0,X0) ) ),
    inference(forward_demodulation,[],[f170,f137])).

fof(f137,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f135,f134])).

fof(f134,plain,(
    sK2 = sK8(sK0,sK1,sK2) ),
    inference(resolution,[],[f54,f115])).

fof(f115,plain,(
    ! [X6,X0,X1] :
      ( ~ r2_hidden(X6,k1_funct_2(X0,X1))
      | sK8(X0,X1,X6) = X6 ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X6,X2,X0,X1] :
      ( sK8(X0,X1,X6) = X6
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f53])).

% (9579)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X1)
                | k1_relat_1(X4) != X0
                | sK6(X0,X1,X2) != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( r1_tarski(k2_relat_1(sK7(X0,X1,X2)),X1)
              & k1_relat_1(sK7(X0,X1,X2)) = X0
              & sK6(X0,X1,X2) = sK7(X0,X1,X2)
              & v1_funct_1(sK7(X0,X1,X2))
              & v1_relat_1(sK7(X0,X1,X2)) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X1)
                  | k1_relat_1(X7) != X0
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ( r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X1)
                & k1_relat_1(sK8(X0,X1,X6)) = X0
                & sK8(X0,X1,X6) = X6
                & v1_funct_1(sK8(X0,X1,X6))
                & v1_relat_1(sK8(X0,X1,X6)) )
              | ~ r2_hidden(X6,X2) ) )
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f49,f52,f51,f50])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X1)
                | k1_relat_1(X4) != X0
                | X3 != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r1_tarski(k2_relat_1(X5),X1)
                & k1_relat_1(X5) = X0
                & X3 = X5
                & v1_funct_1(X5)
                & v1_relat_1(X5) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r1_tarski(k2_relat_1(X4),X1)
              | k1_relat_1(X4) != X0
              | sK6(X0,X1,X2) != X4
              | ~ v1_funct_1(X4)
              | ~ v1_relat_1(X4) )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r1_tarski(k2_relat_1(X5),X1)
              & k1_relat_1(X5) = X0
              & sK6(X0,X1,X2) = X5
              & v1_funct_1(X5)
              & v1_relat_1(X5) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r1_tarski(k2_relat_1(X5),X1)
          & k1_relat_1(X5) = X0
          & sK6(X0,X1,X2) = X5
          & v1_funct_1(X5)
          & v1_relat_1(X5) )
     => ( r1_tarski(k2_relat_1(sK7(X0,X1,X2)),X1)
        & k1_relat_1(sK7(X0,X1,X2)) = X0
        & sK6(X0,X1,X2) = sK7(X0,X1,X2)
        & v1_funct_1(sK7(X0,X1,X2))
        & v1_relat_1(sK7(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r1_tarski(k2_relat_1(X8),X1)
          & k1_relat_1(X8) = X0
          & X6 = X8
          & v1_funct_1(X8)
          & v1_relat_1(X8) )
     => ( r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X1)
        & k1_relat_1(sK8(X0,X1,X6)) = X0
        & sK8(X0,X1,X6) = X6
        & v1_funct_1(sK8(X0,X1,X6))
        & v1_relat_1(sK8(X0,X1,X6)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X1)
                  | k1_relat_1(X4) != X0
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X5] :
                  ( r1_tarski(k2_relat_1(X5),X1)
                  & k1_relat_1(X5) = X0
                  & X3 = X5
                  & v1_funct_1(X5)
                  & v1_relat_1(X5) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X1)
                  | k1_relat_1(X7) != X0
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ? [X8] :
                  ( r1_tarski(k2_relat_1(X8),X1)
                  & k1_relat_1(X8) = X0
                  & X6 = X8
                  & v1_funct_1(X8)
                  & v1_relat_1(X8) )
              | ~ r2_hidden(X6,X2) ) )
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X1)
                  | k1_relat_1(X4) != X0
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4] :
                  ( r1_tarski(k2_relat_1(X4),X1)
                  & k1_relat_1(X4) = X0
                  & X3 = X4
                  & v1_funct_1(X4)
                  & v1_relat_1(X4) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X1)
                  | k1_relat_1(X4) != X0
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) ) )
            & ( ? [X4] :
                  ( r1_tarski(k2_relat_1(X4),X1)
                  & k1_relat_1(X4) = X0
                  & X3 = X4
                  & v1_funct_1(X4)
                  & v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) ) )
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f11])).

% (9562)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% (9564)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r1_tarski(k2_relat_1(X4),X1)
              & k1_relat_1(X4) = X0
              & X3 = X4
              & v1_funct_1(X4)
              & v1_relat_1(X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).

fof(f54,plain,(
    r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) )
    & r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f32])).

fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2) )
        & r2_hidden(X2,k1_funct_2(X0,X1)) )
   => ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
      & r2_hidden(sK2,k1_funct_2(sK0,sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

fof(f135,plain,(
    sK0 = k1_relat_1(sK8(sK0,sK1,sK2)) ),
    inference(resolution,[],[f54,f114])).

fof(f114,plain,(
    ! [X6,X0,X1] :
      ( ~ r2_hidden(X6,k1_funct_2(X0,X1))
      | k1_relat_1(sK8(X0,X1,X6)) = X0 ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_relat_1(sK8(X0,X1,X6)) = X0
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f170,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK0,X0,sK2),sK0)
      | v1_funct_2(sK2,k1_relat_1(sK2),X0) ) ),
    inference(forward_demodulation,[],[f169,f137])).

fof(f169,plain,(
    ! [X0] :
      ( r2_hidden(sK5(k1_relat_1(sK2),X0,sK2),k1_relat_1(sK2))
      | v1_funct_2(sK2,k1_relat_1(sK2),X0) ) ),
    inference(subsumption_resolution,[],[f163,f153])).

fof(f153,plain,(
    v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f146,f54])).

fof(f146,plain,
    ( v1_funct_1(sK2)
    | ~ r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    inference(superposition,[],[f116,f134])).

fof(f116,plain,(
    ! [X6,X0,X1] :
      ( v1_funct_1(sK8(X0,X1,X6))
      | ~ r2_hidden(X6,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_funct_1(sK8(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f163,plain,(
    ! [X0] :
      ( r2_hidden(sK5(k1_relat_1(sK2),X0,sK2),k1_relat_1(sK2))
      | ~ v1_funct_1(sK2)
      | v1_funct_2(sK2,k1_relat_1(sK2),X0) ) ),
    inference(resolution,[],[f148,f106])).

fof(f106,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(sK5(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | v1_funct_2(X2,k1_relat_1(X2),X1) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | r2_hidden(sK5(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ( ~ r2_hidden(k1_funct_1(X2,sK5(X0,X1,X2)),X1)
        & r2_hidden(sK5(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f46])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK5(X0,X1,X2)),X1)
        & r2_hidden(sK5(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( ! [X3] :
              ( r2_hidden(X3,X0)
             => r2_hidden(k1_funct_1(X2,X3),X1) )
          & k1_relat_1(X2) = X0 )
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).

fof(f148,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f145,f54])).

fof(f145,plain,
    ( v1_relat_1(sK2)
    | ~ r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    inference(superposition,[],[f117,f134])).

fof(f117,plain,(
    ! [X6,X0,X1] :
      ( v1_relat_1(sK8(X0,X1,X6))
      | ~ r2_hidden(X6,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_relat_1(sK8(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f349,plain,
    ( spl9_2
    | ~ spl9_3
    | ~ spl9_23 ),
    inference(avatar_contradiction_clause,[],[f348])).

fof(f348,plain,
    ( $false
    | spl9_2
    | ~ spl9_3
    | ~ spl9_23 ),
    inference(subsumption_resolution,[],[f347,f125])).

fof(f347,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl9_3
    | ~ spl9_23 ),
    inference(subsumption_resolution,[],[f346,f153])).

fof(f346,plain,
    ( ~ v1_funct_1(sK2)
    | v1_funct_2(sK2,sK0,sK1)
    | ~ spl9_3
    | ~ spl9_23 ),
    inference(subsumption_resolution,[],[f342,f329])).

fof(f329,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ spl9_23 ),
    inference(avatar_component_clause,[],[f327])).

fof(f327,plain,
    ( spl9_23
  <=> v1_partfun1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f342,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | ~ v1_funct_1(sK2)
    | v1_funct_2(sK2,sK0,sK1)
    | ~ spl9_3 ),
    inference(resolution,[],[f128,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f128,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl9_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f339,plain,
    ( ~ spl9_24
    | spl9_25 ),
    inference(avatar_split_clause,[],[f210,f337,f332])).

fof(f332,plain,
    ( spl9_24
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f210,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ v1_xboole_0(sK2) ) ),
    inference(resolution,[],[f155,f64])).

fof(f64,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f155,plain,(
    ! [X4] :
      ( r2_hidden(k4_tarski(X4,k1_funct_1(sK2,X4)),sK2)
      | ~ r2_hidden(X4,sK0) ) ),
    inference(subsumption_resolution,[],[f154,f148])).

fof(f154,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK0)
      | r2_hidden(k4_tarski(X4,k1_funct_1(sK2,X4)),sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f142,f153])).

fof(f142,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK0)
      | r2_hidden(k4_tarski(X4,k1_funct_1(sK2,X4)),sK2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f100,f137])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

fof(f335,plain,
    ( ~ spl9_22
    | spl9_24 ),
    inference(avatar_split_clause,[],[f215,f332,f323])).

fof(f323,plain,
    ( spl9_22
  <=> v1_xboole_0(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f215,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(k2_relat_1(sK2)) ),
    inference(resolution,[],[f182,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f182,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2)))) ),
    inference(forward_demodulation,[],[f181,f137])).

fof(f181,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    inference(subsumption_resolution,[],[f168,f153])).

fof(f168,plain,
    ( ~ v1_funct_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    inference(resolution,[],[f148,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f330,plain,
    ( spl9_22
    | spl9_23 ),
    inference(avatar_split_clause,[],[f220,f327,f323])).

fof(f220,plain,
    ( v1_partfun1(sK2,sK0)
    | v1_xboole_0(k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f219,f153])).

fof(f219,plain,
    ( ~ v1_funct_1(sK2)
    | v1_partfun1(sK2,sK0)
    | v1_xboole_0(k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f216,f180])).

fof(f180,plain,(
    v1_funct_2(sK2,sK0,k2_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f179,f137])).

fof(f179,plain,(
    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f167,f153])).

fof(f167,plain,
    ( ~ v1_funct_1(sK2)
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    inference(resolution,[],[f148,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f216,plain,
    ( ~ v1_funct_2(sK2,sK0,k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | v1_partfun1(sK2,sK0)
    | v1_xboole_0(k2_relat_1(sK2)) ),
    inference(resolution,[],[f182,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_partfun1(X2,X0)
      | v1_xboole_0(X1) ) ),
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

fof(f318,plain,(
    spl9_3 ),
    inference(avatar_contradiction_clause,[],[f317])).

fof(f317,plain,
    ( $false
    | spl9_3 ),
    inference(subsumption_resolution,[],[f312,f102])).

fof(f102,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f312,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl9_3 ),
    inference(resolution,[],[f191,f129])).

fof(f129,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl9_3 ),
    inference(avatar_component_clause,[],[f127])).

fof(f191,plain,(
    ! [X0] :
      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | ~ r1_tarski(sK0,X0) ) ),
    inference(forward_demodulation,[],[f190,f137])).

fof(f190,plain,(
    ! [X0] :
      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | ~ r1_tarski(k1_relat_1(sK2),X0) ) ),
    inference(subsumption_resolution,[],[f184,f148])).

fof(f184,plain,(
    ! [X0] :
      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | ~ r1_tarski(k1_relat_1(sK2),X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f152,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f152,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(subsumption_resolution,[],[f147,f54])).

fof(f147,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    inference(superposition,[],[f113,f134])).

fof(f113,plain,(
    ! [X6,X0,X1] :
      ( r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X1)
      | ~ r2_hidden(X6,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X1)
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f151,plain,(
    spl9_1 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | spl9_1 ),
    inference(subsumption_resolution,[],[f149,f54])).

fof(f149,plain,
    ( ~ r2_hidden(sK2,k1_funct_2(sK0,sK1))
    | spl9_1 ),
    inference(subsumption_resolution,[],[f146,f121])).

fof(f121,plain,
    ( ~ v1_funct_1(sK2)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl9_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f130,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f55,f127,f123,f119])).

fof(f55,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:30:33 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (9569)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (9569)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (9561)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (9570)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (9566)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (9563)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (9582)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (9567)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (9577)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f446,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f130,f151,f318,f330,f335,f339,f349,f445])).
% 0.21/0.52  fof(f445,plain,(
% 0.21/0.52    spl9_2 | ~spl9_25),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f440])).
% 0.21/0.52  fof(f440,plain,(
% 0.21/0.52    $false | (spl9_2 | ~spl9_25)),
% 0.21/0.52    inference(resolution,[],[f438,f125])).
% 0.21/0.52  fof(f125,plain,(
% 0.21/0.52    ~v1_funct_2(sK2,sK0,sK1) | spl9_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f123])).
% 0.21/0.52  fof(f123,plain,(
% 0.21/0.52    spl9_2 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.21/0.52  fof(f438,plain,(
% 0.21/0.52    ( ! [X0] : (v1_funct_2(sK2,sK0,X0)) ) | ~spl9_25),
% 0.21/0.52    inference(resolution,[],[f171,f338])).
% 0.21/0.52  fof(f338,plain,(
% 0.21/0.52    ( ! [X1] : (~r2_hidden(X1,sK0)) ) | ~spl9_25),
% 0.21/0.52    inference(avatar_component_clause,[],[f337])).
% 0.21/0.52  fof(f337,plain,(
% 0.21/0.52    spl9_25 <=> ! [X1] : ~r2_hidden(X1,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).
% 0.21/0.52  fof(f171,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(sK5(sK0,X0,sK2),sK0) | v1_funct_2(sK2,sK0,X0)) )),
% 0.21/0.52    inference(forward_demodulation,[],[f170,f137])).
% 0.21/0.52  fof(f137,plain,(
% 0.21/0.52    sK0 = k1_relat_1(sK2)),
% 0.21/0.52    inference(forward_demodulation,[],[f135,f134])).
% 0.21/0.53  fof(f134,plain,(
% 0.21/0.53    sK2 = sK8(sK0,sK1,sK2)),
% 0.21/0.53    inference(resolution,[],[f54,f115])).
% 0.21/0.53  fof(f115,plain,(
% 0.21/0.53    ( ! [X6,X0,X1] : (~r2_hidden(X6,k1_funct_2(X0,X1)) | sK8(X0,X1,X6) = X6) )),
% 0.21/0.53    inference(equality_resolution,[],[f88])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    ( ! [X6,X2,X0,X1] : (sK8(X0,X1,X6) = X6 | ~r2_hidden(X6,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f53])).
% 0.21/0.53  % (9579)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | sK6(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((r1_tarski(k2_relat_1(sK7(X0,X1,X2)),X1) & k1_relat_1(sK7(X0,X1,X2)) = X0 & sK6(X0,X1,X2) = sK7(X0,X1,X2) & v1_funct_1(sK7(X0,X1,X2)) & v1_relat_1(sK7(X0,X1,X2))) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X1) | k1_relat_1(X7) != X0 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & ((r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X1) & k1_relat_1(sK8(X0,X1,X6)) = X0 & sK8(X0,X1,X6) = X6 & v1_funct_1(sK8(X0,X1,X6)) & v1_relat_1(sK8(X0,X1,X6))) | ~r2_hidden(X6,X2))) | k1_funct_2(X0,X1) != X2))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f49,f52,f51,f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X1) & k1_relat_1(X5) = X0 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2))) => ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | sK6(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X1) & k1_relat_1(X5) = X0 & sK6(X0,X1,X2) = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ! [X2,X1,X0] : (? [X5] : (r1_tarski(k2_relat_1(X5),X1) & k1_relat_1(X5) = X0 & sK6(X0,X1,X2) = X5 & v1_funct_1(X5) & v1_relat_1(X5)) => (r1_tarski(k2_relat_1(sK7(X0,X1,X2)),X1) & k1_relat_1(sK7(X0,X1,X2)) = X0 & sK6(X0,X1,X2) = sK7(X0,X1,X2) & v1_funct_1(sK7(X0,X1,X2)) & v1_relat_1(sK7(X0,X1,X2))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ! [X6,X1,X0] : (? [X8] : (r1_tarski(k2_relat_1(X8),X1) & k1_relat_1(X8) = X0 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) => (r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X1) & k1_relat_1(sK8(X0,X1,X6)) = X0 & sK8(X0,X1,X6) = X6 & v1_funct_1(sK8(X0,X1,X6)) & v1_relat_1(sK8(X0,X1,X6))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X1) & k1_relat_1(X5) = X0 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X1) | k1_relat_1(X7) != X0 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & (? [X8] : (r1_tarski(k2_relat_1(X8),X1) & k1_relat_1(X8) = X0 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) | ~r2_hidden(X6,X2))) | k1_funct_2(X0,X1) != X2))),
% 0.21/0.53    inference(rectify,[],[f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4))) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | ~r2_hidden(X3,X2))) | k1_funct_2(X0,X1) != X2))),
% 0.21/0.53    inference(nnf_transformation,[],[f11])).
% 0.21/0.53  % (9562)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (9564)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    r2_hidden(sK2,k1_funct_2(sK0,sK1))),
% 0.21/0.53    inference(cnf_transformation,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) & r2_hidden(sK2,k1_funct_2(sK0,sK1))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1))) => ((~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) & r2_hidden(sK2,k1_funct_2(sK0,sK1)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.53    inference(negated_conjecture,[],[f14])).
% 0.21/0.53  fof(f14,conjecture,(
% 0.21/0.53    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).
% 0.21/0.53  fof(f135,plain,(
% 0.21/0.53    sK0 = k1_relat_1(sK8(sK0,sK1,sK2))),
% 0.21/0.53    inference(resolution,[],[f54,f114])).
% 0.21/0.53  fof(f114,plain,(
% 0.21/0.53    ( ! [X6,X0,X1] : (~r2_hidden(X6,k1_funct_2(X0,X1)) | k1_relat_1(sK8(X0,X1,X6)) = X0) )),
% 0.21/0.53    inference(equality_resolution,[],[f89])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    ( ! [X6,X2,X0,X1] : (k1_relat_1(sK8(X0,X1,X6)) = X0 | ~r2_hidden(X6,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f53])).
% 0.21/0.53  fof(f170,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK5(sK0,X0,sK2),sK0) | v1_funct_2(sK2,k1_relat_1(sK2),X0)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f169,f137])).
% 0.21/0.53  fof(f169,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK5(k1_relat_1(sK2),X0,sK2),k1_relat_1(sK2)) | v1_funct_2(sK2,k1_relat_1(sK2),X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f163,f153])).
% 0.21/0.53  fof(f153,plain,(
% 0.21/0.53    v1_funct_1(sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f146,f54])).
% 0.21/0.53  fof(f146,plain,(
% 0.21/0.53    v1_funct_1(sK2) | ~r2_hidden(sK2,k1_funct_2(sK0,sK1))),
% 0.21/0.53    inference(superposition,[],[f116,f134])).
% 0.21/0.53  fof(f116,plain,(
% 0.21/0.53    ( ! [X6,X0,X1] : (v1_funct_1(sK8(X0,X1,X6)) | ~r2_hidden(X6,k1_funct_2(X0,X1))) )),
% 0.21/0.53    inference(equality_resolution,[],[f87])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    ( ! [X6,X2,X0,X1] : (v1_funct_1(sK8(X0,X1,X6)) | ~r2_hidden(X6,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f53])).
% 0.21/0.53  fof(f163,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK5(k1_relat_1(sK2),X0,sK2),k1_relat_1(sK2)) | ~v1_funct_1(sK2) | v1_funct_2(sK2,k1_relat_1(sK2),X0)) )),
% 0.21/0.53    inference(resolution,[],[f148,f106])).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    ( ! [X2,X1] : (~v1_relat_1(X2) | r2_hidden(sK5(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | v1_funct_2(X2,k1_relat_1(X2),X1)) )),
% 0.21/0.53    inference(equality_resolution,[],[f82])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | r2_hidden(sK5(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~r2_hidden(k1_funct_1(X2,sK5(X0,X1,X2)),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK5(X0,X1,X2)),X1) & r2_hidden(sK5(X0,X1,X2),X0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.53    inference(flattening,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).
% 0.21/0.53  fof(f148,plain,(
% 0.21/0.53    v1_relat_1(sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f145,f54])).
% 0.21/0.53  fof(f145,plain,(
% 0.21/0.53    v1_relat_1(sK2) | ~r2_hidden(sK2,k1_funct_2(sK0,sK1))),
% 0.21/0.53    inference(superposition,[],[f117,f134])).
% 0.21/0.53  fof(f117,plain,(
% 0.21/0.53    ( ! [X6,X0,X1] : (v1_relat_1(sK8(X0,X1,X6)) | ~r2_hidden(X6,k1_funct_2(X0,X1))) )),
% 0.21/0.53    inference(equality_resolution,[],[f86])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    ( ! [X6,X2,X0,X1] : (v1_relat_1(sK8(X0,X1,X6)) | ~r2_hidden(X6,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f53])).
% 0.21/0.53  fof(f349,plain,(
% 0.21/0.53    spl9_2 | ~spl9_3 | ~spl9_23),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f348])).
% 0.21/0.53  fof(f348,plain,(
% 0.21/0.53    $false | (spl9_2 | ~spl9_3 | ~spl9_23)),
% 0.21/0.53    inference(subsumption_resolution,[],[f347,f125])).
% 0.21/0.53  fof(f347,plain,(
% 0.21/0.53    v1_funct_2(sK2,sK0,sK1) | (~spl9_3 | ~spl9_23)),
% 0.21/0.53    inference(subsumption_resolution,[],[f346,f153])).
% 0.21/0.53  fof(f346,plain,(
% 0.21/0.53    ~v1_funct_1(sK2) | v1_funct_2(sK2,sK0,sK1) | (~spl9_3 | ~spl9_23)),
% 0.21/0.53    inference(subsumption_resolution,[],[f342,f329])).
% 0.21/0.53  fof(f329,plain,(
% 0.21/0.53    v1_partfun1(sK2,sK0) | ~spl9_23),
% 0.21/0.53    inference(avatar_component_clause,[],[f327])).
% 0.21/0.53  fof(f327,plain,(
% 0.21/0.53    spl9_23 <=> v1_partfun1(sK2,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).
% 0.21/0.53  fof(f342,plain,(
% 0.21/0.53    ~v1_partfun1(sK2,sK0) | ~v1_funct_1(sK2) | v1_funct_2(sK2,sK0,sK1) | ~spl9_3),
% 0.21/0.53    inference(resolution,[],[f128,f79])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | v1_funct_2(X2,X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(flattening,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).
% 0.21/0.53  fof(f128,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl9_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f127])).
% 0.21/0.53  fof(f127,plain,(
% 0.21/0.53    spl9_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.21/0.53  fof(f339,plain,(
% 0.21/0.53    ~spl9_24 | spl9_25),
% 0.21/0.53    inference(avatar_split_clause,[],[f210,f337,f332])).
% 0.21/0.53  fof(f332,plain,(
% 0.21/0.53    spl9_24 <=> v1_xboole_0(sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).
% 0.21/0.53  fof(f210,plain,(
% 0.21/0.53    ( ! [X1] : (~r2_hidden(X1,sK0) | ~v1_xboole_0(sK2)) )),
% 0.21/0.53    inference(resolution,[],[f155,f64])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.53    inference(rectify,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.53    inference(nnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.53  fof(f155,plain,(
% 0.21/0.53    ( ! [X4] : (r2_hidden(k4_tarski(X4,k1_funct_1(sK2,X4)),sK2) | ~r2_hidden(X4,sK0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f154,f148])).
% 0.21/0.53  fof(f154,plain,(
% 0.21/0.53    ( ! [X4] : (~r2_hidden(X4,sK0) | r2_hidden(k4_tarski(X4,k1_funct_1(sK2,X4)),sK2) | ~v1_relat_1(sK2)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f142,f153])).
% 0.21/0.53  fof(f142,plain,(
% 0.21/0.53    ( ! [X4] : (~r2_hidden(X4,sK0) | r2_hidden(k4_tarski(X4,k1_funct_1(sK2,X4)),sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.21/0.53    inference(superposition,[],[f100,f137])).
% 0.21/0.53  fof(f100,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X1,k1_relat_1(X0)) | r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2 | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).
% 0.21/0.53  fof(f335,plain,(
% 0.21/0.53    ~spl9_22 | spl9_24),
% 0.21/0.53    inference(avatar_split_clause,[],[f215,f332,f323])).
% 0.21/0.53  fof(f323,plain,(
% 0.21/0.53    spl9_22 <=> v1_xboole_0(k2_relat_1(sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).
% 0.21/0.53  fof(f215,plain,(
% 0.21/0.53    v1_xboole_0(sK2) | ~v1_xboole_0(k2_relat_1(sK2))),
% 0.21/0.53    inference(resolution,[],[f182,f68])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2) | ~v1_xboole_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.21/0.53  fof(f182,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2))))),
% 0.21/0.53    inference(forward_demodulation,[],[f181,f137])).
% 0.21/0.53  fof(f181,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 0.21/0.53    inference(subsumption_resolution,[],[f168,f153])).
% 0.21/0.53  fof(f168,plain,(
% 0.21/0.53    ~v1_funct_1(sK2) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 0.21/0.53    inference(resolution,[],[f148,f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 0.21/0.53  fof(f330,plain,(
% 0.21/0.53    spl9_22 | spl9_23),
% 0.21/0.53    inference(avatar_split_clause,[],[f220,f327,f323])).
% 0.21/0.53  fof(f220,plain,(
% 0.21/0.53    v1_partfun1(sK2,sK0) | v1_xboole_0(k2_relat_1(sK2))),
% 0.21/0.53    inference(subsumption_resolution,[],[f219,f153])).
% 0.21/0.53  fof(f219,plain,(
% 0.21/0.53    ~v1_funct_1(sK2) | v1_partfun1(sK2,sK0) | v1_xboole_0(k2_relat_1(sK2))),
% 0.21/0.53    inference(subsumption_resolution,[],[f216,f180])).
% 0.21/0.53  fof(f180,plain,(
% 0.21/0.53    v1_funct_2(sK2,sK0,k2_relat_1(sK2))),
% 0.21/0.53    inference(forward_demodulation,[],[f179,f137])).
% 0.21/0.53  fof(f179,plain,(
% 0.21/0.53    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 0.21/0.53    inference(subsumption_resolution,[],[f167,f153])).
% 0.21/0.53  fof(f167,plain,(
% 0.21/0.53    ~v1_funct_1(sK2) | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 0.21/0.53    inference(resolution,[],[f148,f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f216,plain,(
% 0.21/0.53    ~v1_funct_2(sK2,sK0,k2_relat_1(sK2)) | ~v1_funct_1(sK2) | v1_partfun1(sK2,sK0) | v1_xboole_0(k2_relat_1(sK2))),
% 0.21/0.53    inference(resolution,[],[f182,f67])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_partfun1(X2,X0) | v1_xboole_0(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.53    inference(flattening,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.21/0.53  fof(f318,plain,(
% 0.21/0.53    spl9_3),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f317])).
% 0.21/0.53  fof(f317,plain,(
% 0.21/0.53    $false | spl9_3),
% 0.21/0.53    inference(subsumption_resolution,[],[f312,f102])).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.53    inference(equality_resolution,[],[f69])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.53    inference(flattening,[],[f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.53  fof(f312,plain,(
% 0.21/0.53    ~r1_tarski(sK0,sK0) | spl9_3),
% 0.21/0.53    inference(resolution,[],[f191,f129])).
% 0.21/0.53  fof(f129,plain,(
% 0.21/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl9_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f127])).
% 0.21/0.53  fof(f191,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | ~r1_tarski(sK0,X0)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f190,f137])).
% 0.21/0.53  fof(f190,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | ~r1_tarski(k1_relat_1(sK2),X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f184,f148])).
% 0.21/0.53  fof(f184,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | ~r1_tarski(k1_relat_1(sK2),X0) | ~v1_relat_1(sK2)) )),
% 0.21/0.53    inference(resolution,[],[f152,f77])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.21/0.53    inference(flattening,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 0.21/0.53  fof(f152,plain,(
% 0.21/0.53    r1_tarski(k2_relat_1(sK2),sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f147,f54])).
% 0.21/0.53  fof(f147,plain,(
% 0.21/0.53    r1_tarski(k2_relat_1(sK2),sK1) | ~r2_hidden(sK2,k1_funct_2(sK0,sK1))),
% 0.21/0.53    inference(superposition,[],[f113,f134])).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    ( ! [X6,X0,X1] : (r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X1) | ~r2_hidden(X6,k1_funct_2(X0,X1))) )),
% 0.21/0.53    inference(equality_resolution,[],[f90])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    ( ! [X6,X2,X0,X1] : (r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X1) | ~r2_hidden(X6,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f53])).
% 0.21/0.53  fof(f151,plain,(
% 0.21/0.53    spl9_1),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f150])).
% 0.21/0.53  fof(f150,plain,(
% 0.21/0.53    $false | spl9_1),
% 0.21/0.53    inference(subsumption_resolution,[],[f149,f54])).
% 0.21/0.53  fof(f149,plain,(
% 0.21/0.53    ~r2_hidden(sK2,k1_funct_2(sK0,sK1)) | spl9_1),
% 0.21/0.53    inference(subsumption_resolution,[],[f146,f121])).
% 0.21/0.53  fof(f121,plain,(
% 0.21/0.53    ~v1_funct_1(sK2) | spl9_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f119])).
% 0.21/0.53  fof(f119,plain,(
% 0.21/0.53    spl9_1 <=> v1_funct_1(sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.21/0.53  fof(f130,plain,(
% 0.21/0.53    ~spl9_1 | ~spl9_2 | ~spl9_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f55,f127,f123,f119])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f33])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (9569)------------------------------
% 0.21/0.53  % (9569)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (9569)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (9569)Memory used [KB]: 10874
% 0.21/0.53  % (9569)Time elapsed: 0.097 s
% 0.21/0.53  % (9569)------------------------------
% 0.21/0.53  % (9569)------------------------------
% 0.21/0.53  % (9557)Success in time 0.171 s
%------------------------------------------------------------------------------
