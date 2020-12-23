%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 387 expanded)
%              Number of leaves         :   20 ( 103 expanded)
%              Depth                    :   15
%              Number of atoms          :  530 (2002 expanded)
%              Number of equality atoms :   64 ( 523 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f319,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f122,f145,f193,f210,f217,f227,f287,f318])).

fof(f318,plain,(
    spl4_11 ),
    inference(avatar_contradiction_clause,[],[f317])).

fof(f317,plain,
    ( $false
    | spl4_11 ),
    inference(subsumption_resolution,[],[f316,f39])).

fof(f39,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0)
      | sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) )
    & r2_hidden(sK0,k1_relat_1(sK1))
    & v2_funct_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f29])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0
          | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0 )
        & r2_hidden(X0,k1_relat_1(X1))
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0)
        | sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) )
      & r2_hidden(sK0,k1_relat_1(sK1))
      & v2_funct_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0
        | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0 )
      & r2_hidden(X0,k1_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0
        | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0 )
      & r2_hidden(X0,k1_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( r2_hidden(X0,k1_relat_1(X1))
            & v2_funct_1(X1) )
         => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
            & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).

fof(f316,plain,
    ( ~ v1_relat_1(sK1)
    | spl4_11 ),
    inference(subsumption_resolution,[],[f315,f40])).

fof(f40,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f315,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_11 ),
    inference(subsumption_resolution,[],[f314,f42])).

fof(f42,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f314,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_11 ),
    inference(resolution,[],[f286,f54])).

% (25358)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

fof(f286,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f285])).

fof(f285,plain,
    ( spl4_11
  <=> r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f287,plain,
    ( ~ spl4_3
    | ~ spl4_11
    | spl4_7 ),
    inference(avatar_split_clause,[],[f283,f208,f285,f117])).

fof(f117,plain,
    ( spl4_3
  <=> v1_funct_1(k4_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f208,plain,
    ( spl4_7
  <=> r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f283,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | ~ v1_funct_1(k4_relat_1(sK1))
    | spl4_7 ),
    inference(subsumption_resolution,[],[f282,f39])).

fof(f282,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(k4_relat_1(sK1))
    | spl4_7 ),
    inference(subsumption_resolution,[],[f281,f40])).

fof(f281,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(k4_relat_1(sK1))
    | spl4_7 ),
    inference(subsumption_resolution,[],[f280,f42])).

fof(f280,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(k4_relat_1(sK1))
    | spl4_7 ),
    inference(duplicate_literal_removal,[],[f279])).

fof(f279,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(k4_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | spl4_7 ),
    inference(resolution,[],[f243,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_relat_1(k5_relat_1(X1,k4_relat_1(X0))))
      | ~ r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X0))
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f98,f44])).

fof(f44,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

% (25378)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X0))
      | r2_hidden(X2,k1_relat_1(k5_relat_1(X1,k4_relat_1(X0))))
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(k4_relat_1(X0))
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f58,f45])).

fof(f45,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
      | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
              | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2)) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
              | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2)) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_1)).

fof(f243,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k4_relat_1(sK1))))
    | spl4_7 ),
    inference(subsumption_resolution,[],[f242,f39])).

fof(f242,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k4_relat_1(sK1))))
    | ~ v1_relat_1(sK1)
    | spl4_7 ),
    inference(subsumption_resolution,[],[f241,f40])).

fof(f241,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k4_relat_1(sK1))))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_7 ),
    inference(subsumption_resolution,[],[f240,f41])).

fof(f41,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f240,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k4_relat_1(sK1))))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_7 ),
    inference(superposition,[],[f209,f53])).

fof(f53,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f209,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1))))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f208])).

fof(f227,plain,(
    spl4_6 ),
    inference(avatar_contradiction_clause,[],[f226])).

fof(f226,plain,
    ( $false
    | spl4_6 ),
    inference(subsumption_resolution,[],[f225,f39])).

fof(f225,plain,
    ( ~ v1_relat_1(sK1)
    | spl4_6 ),
    inference(subsumption_resolution,[],[f224,f40])).

fof(f224,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_6 ),
    inference(subsumption_resolution,[],[f223,f41])).

fof(f223,plain,
    ( ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_6 ),
    inference(resolution,[],[f221,f52])).

fof(f52,plain,(
    ! [X0] :
      ( v1_funct_1(k4_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_funct_1(k4_relat_1(X0))
        & v1_relat_1(k4_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_funct_1(k4_relat_1(X0))
        & v1_relat_1(k4_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k4_relat_1(X0))
        & v1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_funct_1)).

fof(f221,plain,
    ( ~ v1_funct_1(k4_relat_1(sK1))
    | spl4_6 ),
    inference(subsumption_resolution,[],[f220,f39])).

fof(f220,plain,
    ( ~ v1_funct_1(k4_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | spl4_6 ),
    inference(subsumption_resolution,[],[f219,f40])).

fof(f219,plain,
    ( ~ v1_funct_1(k4_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_6 ),
    inference(subsumption_resolution,[],[f218,f41])).

fof(f218,plain,
    ( ~ v1_funct_1(k4_relat_1(sK1))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_6 ),
    inference(superposition,[],[f206,f53])).

fof(f206,plain,
    ( ~ v1_funct_1(k2_funct_1(sK1))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl4_6
  <=> v1_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f217,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f216])).

fof(f216,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f215,f39])).

fof(f215,plain,
    ( ~ v1_relat_1(sK1)
    | spl4_5 ),
    inference(resolution,[],[f214,f44])).

fof(f214,plain,
    ( ~ v1_relat_1(k4_relat_1(sK1))
    | spl4_5 ),
    inference(subsumption_resolution,[],[f213,f39])).

fof(f213,plain,
    ( ~ v1_relat_1(k4_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | spl4_5 ),
    inference(subsumption_resolution,[],[f212,f40])).

fof(f212,plain,
    ( ~ v1_relat_1(k4_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_5 ),
    inference(subsumption_resolution,[],[f211,f41])).

fof(f211,plain,
    ( ~ v1_relat_1(k4_relat_1(sK1))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_5 ),
    inference(superposition,[],[f203,f53])).

fof(f203,plain,
    ( ~ v1_relat_1(k2_funct_1(sK1))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f202])).

fof(f202,plain,
    ( spl4_5
  <=> v1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f210,plain,
    ( ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f200,f69,f66,f208,f205,f202])).

fof(f66,plain,
    ( spl4_1
  <=> sK0 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f69,plain,
    ( spl4_2
  <=> sK0 = k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f200,plain,
    ( sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))
    | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1))))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | spl4_2 ),
    inference(subsumption_resolution,[],[f199,f39])).

% (25364)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
fof(f199,plain,
    ( sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))
    | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1))))
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | spl4_2 ),
    inference(subsumption_resolution,[],[f195,f40])).

fof(f195,plain,
    ( sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))
    | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1))))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | spl4_2 ),
    inference(superposition,[],[f70,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

fof(f70,plain,
    ( sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f193,plain,(
    ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f192])).

fof(f192,plain,
    ( $false
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f191,f39])).

fof(f191,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f190,f40])).

fof(f190,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f189,f42])).

fof(f189,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f168,f64])).

% (25358)Refutation not found, incomplete strategy% (25358)------------------------------
% (25358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (25358)Termination reason: Refutation not found, incomplete strategy

% (25358)Memory used [KB]: 10618
% (25358)Time elapsed: 0.089 s
% (25358)------------------------------
% (25358)------------------------------
fof(f64,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f61])).

% (25378)Refutation not found, incomplete strategy% (25378)------------------------------
% (25378)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

% (25378)Termination reason: Refutation not found, incomplete strategy
fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

% (25378)Memory used [KB]: 10618
% (25378)Time elapsed: 0.093 s
% (25378)------------------------------
% (25378)------------------------------
fof(f168,plain,
    ( ~ r2_hidden(k4_tarski(sK0,k1_funct_1(sK1,sK0)),sK1)
    | ~ spl4_4 ),
    inference(equality_resolution,[],[f121])).

fof(f121,plain,
    ( ! [X0] :
        ( sK0 != X0
        | ~ r2_hidden(k4_tarski(X0,k1_funct_1(sK1,sK0)),sK1) )
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl4_4
  <=> ! [X0] :
        ( sK0 != X0
        | ~ r2_hidden(k4_tarski(X0,k1_funct_1(sK1,sK0)),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f145,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f144])).

fof(f144,plain,
    ( $false
    | spl4_3 ),
    inference(subsumption_resolution,[],[f143,f39])).

fof(f143,plain,
    ( ~ v1_relat_1(sK1)
    | spl4_3 ),
    inference(subsumption_resolution,[],[f142,f40])).

fof(f142,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_3 ),
    inference(subsumption_resolution,[],[f141,f41])).

fof(f141,plain,
    ( ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_3 ),
    inference(resolution,[],[f118,f52])).

fof(f118,plain,
    ( ~ v1_funct_1(k4_relat_1(sK1))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f117])).

fof(f122,plain,
    ( ~ spl4_3
    | spl4_4
    | spl4_1 ),
    inference(avatar_split_clause,[],[f115,f66,f120,f117])).

fof(f115,plain,
    ( ! [X0] :
        ( sK0 != X0
        | ~ v1_funct_1(k4_relat_1(sK1))
        | ~ r2_hidden(k4_tarski(X0,k1_funct_1(sK1,sK0)),sK1) )
    | spl4_1 ),
    inference(subsumption_resolution,[],[f107,f39])).

fof(f107,plain,
    ( ! [X0] :
        ( sK0 != X0
        | ~ v1_funct_1(k4_relat_1(sK1))
        | ~ r2_hidden(k4_tarski(X0,k1_funct_1(sK1,sK0)),sK1)
        | ~ v1_relat_1(sK1) )
    | spl4_1 ),
    inference(superposition,[],[f77,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k4_relat_1(X0),X1) = X2
      | ~ v1_funct_1(k4_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X2,X1),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f84,f44])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k4_relat_1(X0),X1) = X2
      | ~ v1_funct_1(k4_relat_1(X0))
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X2,X1),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f60,f72])).

fof(f72,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f62,f44])).

fof(f62,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | k4_relat_1(X0) != X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
                  | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
                & ( r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
                  | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f32,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r2_hidden(k4_tarski(X3,X2),X0)
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
          | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
        & ( r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
          | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X2,X3] :
                  ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X3,X2),X0) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

% (25370)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_1)).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f77,plain,
    ( sK0 != k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK0))
    | spl4_1 ),
    inference(subsumption_resolution,[],[f76,f39])).

fof(f76,plain,
    ( sK0 != k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK0))
    | ~ v1_relat_1(sK1)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f75,f40])).

fof(f75,plain,
    ( sK0 != k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f74,f41])).

fof(f74,plain,
    ( sK0 != k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK0))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_1 ),
    inference(superposition,[],[f67,f53])).

fof(f67,plain,
    ( sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f71,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f43,f69,f66])).

fof(f43,plain,
    ( sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0)
    | sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:01:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (25362)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (25357)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (25371)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (25359)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  % (25365)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (25361)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (25373)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (25366)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.49  % (25360)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (25372)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (25359)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f319,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f71,f122,f145,f193,f210,f217,f227,f287,f318])).
% 0.21/0.49  fof(f318,plain,(
% 0.21/0.49    spl4_11),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f317])).
% 0.21/0.49  fof(f317,plain,(
% 0.21/0.49    $false | spl4_11),
% 0.21/0.49    inference(subsumption_resolution,[],[f316,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    v1_relat_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    (sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0) | sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))) & r2_hidden(sK0,k1_relat_1(sK1)) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ? [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0 | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0) & r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => ((sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0) | sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))) & r2_hidden(sK0,k1_relat_1(sK1)) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ? [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0 | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0) & r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ? [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0 | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0) & (r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 0.21/0.49    inference(negated_conjecture,[],[f10])).
% 0.21/0.49  fof(f10,conjecture,(
% 0.21/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).
% 0.21/0.49  fof(f316,plain,(
% 0.21/0.49    ~v1_relat_1(sK1) | spl4_11),
% 0.21/0.49    inference(subsumption_resolution,[],[f315,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    v1_funct_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f315,plain,(
% 0.21/0.49    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_11),
% 0.21/0.49    inference(subsumption_resolution,[],[f314,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f314,plain,(
% 0.21/0.49    ~r2_hidden(sK0,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_11),
% 0.21/0.49    inference(resolution,[],[f286,f54])).
% 0.21/0.49  % (25358)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).
% 0.21/0.49  fof(f286,plain,(
% 0.21/0.49    ~r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) | spl4_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f285])).
% 0.21/0.49  fof(f285,plain,(
% 0.21/0.49    spl4_11 <=> r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.49  fof(f287,plain,(
% 0.21/0.49    ~spl4_3 | ~spl4_11 | spl4_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f283,f208,f285,f117])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    spl4_3 <=> v1_funct_1(k4_relat_1(sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.49  fof(f208,plain,(
% 0.21/0.49    spl4_7 <=> r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.49  fof(f283,plain,(
% 0.21/0.49    ~r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) | ~v1_funct_1(k4_relat_1(sK1)) | spl4_7),
% 0.21/0.49    inference(subsumption_resolution,[],[f282,f39])).
% 0.21/0.49  fof(f282,plain,(
% 0.21/0.49    ~r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) | ~v1_relat_1(sK1) | ~v1_funct_1(k4_relat_1(sK1)) | spl4_7),
% 0.21/0.49    inference(subsumption_resolution,[],[f281,f40])).
% 0.21/0.49  fof(f281,plain,(
% 0.21/0.49    ~r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(k4_relat_1(sK1)) | spl4_7),
% 0.21/0.49    inference(subsumption_resolution,[],[f280,f42])).
% 0.21/0.49  fof(f280,plain,(
% 0.21/0.49    ~r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) | ~r2_hidden(sK0,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(k4_relat_1(sK1)) | spl4_7),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f279])).
% 0.21/0.49  fof(f279,plain,(
% 0.21/0.49    ~r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) | ~r2_hidden(sK0,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(k4_relat_1(sK1)) | ~v1_relat_1(sK1) | spl4_7),
% 0.21/0.49    inference(resolution,[],[f243,f99])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r2_hidden(X2,k1_relat_1(k5_relat_1(X1,k4_relat_1(X0)))) | ~r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X0)) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f98,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.21/0.49  % (25378)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X0)) | r2_hidden(X2,k1_relat_1(k5_relat_1(X1,k4_relat_1(X0)))) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(k4_relat_1(X0)) | ~v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(superposition,[],[f58,f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | (~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2)))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_1)).
% 0.21/0.49  fof(f243,plain,(
% 0.21/0.49    ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k4_relat_1(sK1)))) | spl4_7),
% 0.21/0.49    inference(subsumption_resolution,[],[f242,f39])).
% 0.21/0.49  fof(f242,plain,(
% 0.21/0.49    ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k4_relat_1(sK1)))) | ~v1_relat_1(sK1) | spl4_7),
% 0.21/0.49    inference(subsumption_resolution,[],[f241,f40])).
% 0.21/0.49  fof(f241,plain,(
% 0.21/0.49    ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k4_relat_1(sK1)))) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_7),
% 0.21/0.49    inference(subsumption_resolution,[],[f240,f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    v2_funct_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f240,plain,(
% 0.21/0.49    ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k4_relat_1(sK1)))) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_7),
% 0.21/0.49    inference(superposition,[],[f209,f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.21/0.49  fof(f209,plain,(
% 0.21/0.49    ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1)))) | spl4_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f208])).
% 0.21/0.49  fof(f227,plain,(
% 0.21/0.49    spl4_6),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f226])).
% 0.21/0.49  fof(f226,plain,(
% 0.21/0.49    $false | spl4_6),
% 0.21/0.49    inference(subsumption_resolution,[],[f225,f39])).
% 0.21/0.49  fof(f225,plain,(
% 0.21/0.49    ~v1_relat_1(sK1) | spl4_6),
% 0.21/0.49    inference(subsumption_resolution,[],[f224,f40])).
% 0.21/0.49  fof(f224,plain,(
% 0.21/0.49    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_6),
% 0.21/0.49    inference(subsumption_resolution,[],[f223,f41])).
% 0.21/0.49  fof(f223,plain,(
% 0.21/0.49    ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_6),
% 0.21/0.49    inference(resolution,[],[f221,f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X0] : (v1_funct_1(k4_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(k4_relat_1(X0)) & v1_relat_1(k4_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(k4_relat_1(X0)) & v1_relat_1(k4_relat_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k4_relat_1(X0)) & v1_relat_1(k4_relat_1(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_funct_1)).
% 0.21/0.49  fof(f221,plain,(
% 0.21/0.49    ~v1_funct_1(k4_relat_1(sK1)) | spl4_6),
% 0.21/0.49    inference(subsumption_resolution,[],[f220,f39])).
% 0.21/0.49  fof(f220,plain,(
% 0.21/0.49    ~v1_funct_1(k4_relat_1(sK1)) | ~v1_relat_1(sK1) | spl4_6),
% 0.21/0.49    inference(subsumption_resolution,[],[f219,f40])).
% 0.21/0.49  fof(f219,plain,(
% 0.21/0.49    ~v1_funct_1(k4_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_6),
% 0.21/0.49    inference(subsumption_resolution,[],[f218,f41])).
% 0.21/0.49  fof(f218,plain,(
% 0.21/0.49    ~v1_funct_1(k4_relat_1(sK1)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_6),
% 0.21/0.49    inference(superposition,[],[f206,f53])).
% 0.21/0.49  fof(f206,plain,(
% 0.21/0.49    ~v1_funct_1(k2_funct_1(sK1)) | spl4_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f205])).
% 0.21/0.49  fof(f205,plain,(
% 0.21/0.49    spl4_6 <=> v1_funct_1(k2_funct_1(sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.49  fof(f217,plain,(
% 0.21/0.49    spl4_5),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f216])).
% 0.21/0.49  fof(f216,plain,(
% 0.21/0.49    $false | spl4_5),
% 0.21/0.49    inference(subsumption_resolution,[],[f215,f39])).
% 0.21/0.49  fof(f215,plain,(
% 0.21/0.49    ~v1_relat_1(sK1) | spl4_5),
% 0.21/0.49    inference(resolution,[],[f214,f44])).
% 0.21/0.49  fof(f214,plain,(
% 0.21/0.49    ~v1_relat_1(k4_relat_1(sK1)) | spl4_5),
% 0.21/0.49    inference(subsumption_resolution,[],[f213,f39])).
% 0.21/0.49  fof(f213,plain,(
% 0.21/0.49    ~v1_relat_1(k4_relat_1(sK1)) | ~v1_relat_1(sK1) | spl4_5),
% 0.21/0.49    inference(subsumption_resolution,[],[f212,f40])).
% 0.21/0.49  fof(f212,plain,(
% 0.21/0.49    ~v1_relat_1(k4_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_5),
% 0.21/0.49    inference(subsumption_resolution,[],[f211,f41])).
% 0.21/0.50  fof(f211,plain,(
% 0.21/0.50    ~v1_relat_1(k4_relat_1(sK1)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_5),
% 0.21/0.50    inference(superposition,[],[f203,f53])).
% 0.21/0.50  fof(f203,plain,(
% 0.21/0.50    ~v1_relat_1(k2_funct_1(sK1)) | spl4_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f202])).
% 0.21/0.50  fof(f202,plain,(
% 0.21/0.50    spl4_5 <=> v1_relat_1(k2_funct_1(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.50  fof(f210,plain,(
% 0.21/0.50    ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_1 | spl4_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f200,f69,f66,f208,f205,f202])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    spl4_1 <=> sK0 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    spl4_2 <=> sK0 = k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.50  fof(f200,plain,(
% 0.21/0.50    sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1)))) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | spl4_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f199,f39])).
% 0.21/0.50  % (25364)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  fof(f199,plain,(
% 0.21/0.50    sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1)))) | ~v1_relat_1(sK1) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | spl4_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f195,f40])).
% 0.21/0.50  fof(f195,plain,(
% 0.21/0.50    sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1)))) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | spl4_2),
% 0.21/0.50    inference(superposition,[],[f70,f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0) | spl4_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f69])).
% 0.21/0.50  fof(f193,plain,(
% 0.21/0.50    ~spl4_4),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f192])).
% 0.21/0.50  fof(f192,plain,(
% 0.21/0.50    $false | ~spl4_4),
% 0.21/0.50    inference(subsumption_resolution,[],[f191,f39])).
% 0.21/0.50  fof(f191,plain,(
% 0.21/0.50    ~v1_relat_1(sK1) | ~spl4_4),
% 0.21/0.50    inference(subsumption_resolution,[],[f190,f40])).
% 0.21/0.50  fof(f190,plain,(
% 0.21/0.50    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl4_4),
% 0.21/0.50    inference(subsumption_resolution,[],[f189,f42])).
% 0.21/0.50  fof(f189,plain,(
% 0.21/0.50    ~r2_hidden(sK0,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl4_4),
% 0.21/0.50    inference(resolution,[],[f168,f64])).
% 0.21/0.50  % (25358)Refutation not found, incomplete strategy% (25358)------------------------------
% 0.21/0.50  % (25358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (25358)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (25358)Memory used [KB]: 10618
% 0.21/0.50  % (25358)Time elapsed: 0.089 s
% 0.21/0.50  % (25358)------------------------------
% 0.21/0.50  % (25358)------------------------------
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.50    inference(equality_resolution,[],[f61])).
% 0.21/0.50  % (25378)Refutation not found, incomplete strategy% (25378)------------------------------
% 0.21/0.50  % (25378)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(flattening,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(nnf_transformation,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(flattening,[],[f27])).
% 0.21/0.50  % (25378)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.21/0.50  
% 0.21/0.50  % (25378)Memory used [KB]: 10618
% 0.21/0.50  % (25378)Time elapsed: 0.093 s
% 0.21/0.50  % (25378)------------------------------
% 0.21/0.50  % (25378)------------------------------
% 0.21/0.50  fof(f168,plain,(
% 0.21/0.50    ~r2_hidden(k4_tarski(sK0,k1_funct_1(sK1,sK0)),sK1) | ~spl4_4),
% 0.21/0.50    inference(equality_resolution,[],[f121])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    ( ! [X0] : (sK0 != X0 | ~r2_hidden(k4_tarski(X0,k1_funct_1(sK1,sK0)),sK1)) ) | ~spl4_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f120])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    spl4_4 <=> ! [X0] : (sK0 != X0 | ~r2_hidden(k4_tarski(X0,k1_funct_1(sK1,sK0)),sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.50  fof(f145,plain,(
% 0.21/0.50    spl4_3),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f144])).
% 0.21/0.50  fof(f144,plain,(
% 0.21/0.50    $false | spl4_3),
% 0.21/0.50    inference(subsumption_resolution,[],[f143,f39])).
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    ~v1_relat_1(sK1) | spl4_3),
% 0.21/0.50    inference(subsumption_resolution,[],[f142,f40])).
% 0.21/0.50  fof(f142,plain,(
% 0.21/0.50    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_3),
% 0.21/0.50    inference(subsumption_resolution,[],[f141,f41])).
% 0.21/0.50  fof(f141,plain,(
% 0.21/0.50    ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_3),
% 0.21/0.50    inference(resolution,[],[f118,f52])).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    ~v1_funct_1(k4_relat_1(sK1)) | spl4_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f117])).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    ~spl4_3 | spl4_4 | spl4_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f115,f66,f120,f117])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    ( ! [X0] : (sK0 != X0 | ~v1_funct_1(k4_relat_1(sK1)) | ~r2_hidden(k4_tarski(X0,k1_funct_1(sK1,sK0)),sK1)) ) | spl4_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f107,f39])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    ( ! [X0] : (sK0 != X0 | ~v1_funct_1(k4_relat_1(sK1)) | ~r2_hidden(k4_tarski(X0,k1_funct_1(sK1,sK0)),sK1) | ~v1_relat_1(sK1)) ) | spl4_1),
% 0.21/0.50    inference(superposition,[],[f77,f85])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_funct_1(k4_relat_1(X0),X1) = X2 | ~v1_funct_1(k4_relat_1(X0)) | ~r2_hidden(k4_tarski(X2,X1),X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f84,f44])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_funct_1(k4_relat_1(X0),X1) = X2 | ~v1_funct_1(k4_relat_1(X0)) | ~v1_relat_1(k4_relat_1(X0)) | ~r2_hidden(k4_tarski(X2,X1),X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(resolution,[],[f60,f72])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    ( ! [X4,X0,X5] : (r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X4),X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f62,f44])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X4,X0,X5] : (r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X4),X0) | ~v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X5,X4),X0) | k4_relat_1(X0) != X1 | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((k4_relat_1(X0) = X1 | ((~r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X5,X4),X0)) & (r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k4_relat_1(X0) != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f32,f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X1,X0] : (? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1))) => ((~r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((k4_relat_1(X0) = X1 | ? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X5,X4),X0)) & (r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k4_relat_1(X0) != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(rectify,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((k4_relat_1(X0) = X1 | ? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X3,X2),X0)) & (r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1))) | k4_relat_1(X0) != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((k4_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> r2_hidden(k4_tarski(X3,X2),X0))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  % (25370)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (k4_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> r2_hidden(k4_tarski(X3,X2),X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_1)).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    sK0 != k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK0)) | spl4_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f76,f39])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    sK0 != k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK0)) | ~v1_relat_1(sK1) | spl4_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f75,f40])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    sK0 != k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f74,f41])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    sK0 != k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK0)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_1),
% 0.21/0.50    inference(superposition,[],[f67,f53])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) | spl4_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f66])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    ~spl4_1 | ~spl4_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f43,f69,f66])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0) | sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (25359)------------------------------
% 0.21/0.50  % (25359)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (25359)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (25359)Memory used [KB]: 10874
% 0.21/0.50  % (25359)Time elapsed: 0.084 s
% 0.21/0.50  % (25359)------------------------------
% 0.21/0.50  % (25359)------------------------------
% 0.21/0.50  % (25368)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.50  % (25354)Success in time 0.14 s
%------------------------------------------------------------------------------
