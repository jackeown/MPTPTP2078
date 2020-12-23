%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 479 expanded)
%              Number of leaves         :   10 ( 137 expanded)
%              Depth                    :   29
%              Number of atoms          :  400 (5542 expanded)
%              Number of equality atoms :  127 (2547 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f209,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f204])).

fof(f204,plain,(
    ~ spl3_1 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f202,f48])).

fof(f48,plain,(
    v1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f47,f26])).

fof(f26,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( k2_funct_1(sK0) != sK1
    & ! [X2,X3] :
        ( ( ( k1_funct_1(sK0,X2) = X3
            | k1_funct_1(sK1,X3) != X2 )
          & ( k1_funct_1(sK1,X3) = X2
            | k1_funct_1(sK0,X2) != X3 ) )
        | ~ r2_hidden(X3,k1_relat_1(sK1))
        | ~ r2_hidden(X2,k1_relat_1(sK0)) )
    & k2_relat_1(sK0) = k1_relat_1(sK1)
    & k1_relat_1(sK0) = k2_relat_1(sK1)
    & v2_funct_1(sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_funct_1(X0) != X1
            & ! [X2,X3] :
                ( ( ( k1_funct_1(X0,X2) = X3
                    | k1_funct_1(X1,X3) != X2 )
                  & ( k1_funct_1(X1,X3) = X2
                    | k1_funct_1(X0,X2) != X3 ) )
                | ~ r2_hidden(X3,k1_relat_1(X1))
                | ~ r2_hidden(X2,k1_relat_1(X0)) )
            & k1_relat_1(X1) = k2_relat_1(X0)
            & k2_relat_1(X1) = k1_relat_1(X0)
            & v2_funct_1(X0)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k2_funct_1(sK0) != X1
          & ! [X3,X2] :
              ( ( ( k1_funct_1(sK0,X2) = X3
                  | k1_funct_1(X1,X3) != X2 )
                & ( k1_funct_1(X1,X3) = X2
                  | k1_funct_1(sK0,X2) != X3 ) )
              | ~ r2_hidden(X3,k1_relat_1(X1))
              | ~ r2_hidden(X2,k1_relat_1(sK0)) )
          & k1_relat_1(X1) = k2_relat_1(sK0)
          & k2_relat_1(X1) = k1_relat_1(sK0)
          & v2_funct_1(sK0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( k2_funct_1(sK0) != X1
        & ! [X3,X2] :
            ( ( ( k1_funct_1(sK0,X2) = X3
                | k1_funct_1(X1,X3) != X2 )
              & ( k1_funct_1(X1,X3) = X2
                | k1_funct_1(sK0,X2) != X3 ) )
            | ~ r2_hidden(X3,k1_relat_1(X1))
            | ~ r2_hidden(X2,k1_relat_1(sK0)) )
        & k1_relat_1(X1) = k2_relat_1(sK0)
        & k2_relat_1(X1) = k1_relat_1(sK0)
        & v2_funct_1(sK0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k2_funct_1(sK0) != sK1
      & ! [X3,X2] :
          ( ( ( k1_funct_1(sK0,X2) = X3
              | k1_funct_1(sK1,X3) != X2 )
            & ( k1_funct_1(sK1,X3) = X2
              | k1_funct_1(sK0,X2) != X3 ) )
          | ~ r2_hidden(X3,k1_relat_1(sK1))
          | ~ r2_hidden(X2,k1_relat_1(sK0)) )
      & k2_relat_1(sK0) = k1_relat_1(sK1)
      & k1_relat_1(sK0) = k2_relat_1(sK1)
      & v2_funct_1(sK0)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & ! [X2,X3] :
              ( ( ( k1_funct_1(X0,X2) = X3
                  | k1_funct_1(X1,X3) != X2 )
                & ( k1_funct_1(X1,X3) = X2
                  | k1_funct_1(X0,X2) != X3 ) )
              | ~ r2_hidden(X3,k1_relat_1(X1))
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          & k1_relat_1(X1) = k2_relat_1(X0)
          & k2_relat_1(X1) = k1_relat_1(X0)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & ! [X2,X3] :
              ( ( k1_funct_1(X0,X2) = X3
              <=> k1_funct_1(X1,X3) = X2 )
              | ~ r2_hidden(X3,k1_relat_1(X1))
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          & k1_relat_1(X1) = k2_relat_1(X0)
          & k2_relat_1(X1) = k1_relat_1(X0)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & ! [X2,X3] :
              ( ( k1_funct_1(X0,X2) = X3
              <=> k1_funct_1(X1,X3) = X2 )
              | ~ r2_hidden(X3,k1_relat_1(X1))
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          & k1_relat_1(X1) = k2_relat_1(X0)
          & k2_relat_1(X1) = k1_relat_1(X0)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( ! [X2,X3] :
                    ( ( r2_hidden(X3,k1_relat_1(X1))
                      & r2_hidden(X2,k1_relat_1(X0)) )
                   => ( k1_funct_1(X0,X2) = X3
                    <=> k1_funct_1(X1,X3) = X2 ) )
                & k1_relat_1(X1) = k2_relat_1(X0)
                & k2_relat_1(X1) = k1_relat_1(X0)
                & v2_funct_1(X0) )
             => k2_funct_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2,X3] :
                  ( ( r2_hidden(X3,k1_relat_1(X1))
                    & r2_hidden(X2,k1_relat_1(X0)) )
                 => ( k1_funct_1(X0,X2) = X3
                  <=> k1_funct_1(X1,X3) = X2 ) )
              & k1_relat_1(X1) = k2_relat_1(X0)
              & k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_1)).

fof(f47,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f27,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f27,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f202,plain,
    ( ~ v1_relat_1(k2_funct_1(sK0))
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f201,f68])).

fof(f68,plain,
    ( v1_funct_1(k2_funct_1(sK0))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl3_1
  <=> v1_funct_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f201,plain,
    ( ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f200,f28])).

fof(f28,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f200,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f199,f29])).

fof(f29,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f199,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f198,f63])).

fof(f63,plain,(
    k1_relat_1(sK1) = k1_relat_1(k2_funct_1(sK0)) ),
    inference(forward_demodulation,[],[f54,f32])).

fof(f32,plain,(
    k2_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f54,plain,(
    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f53,f26])).

fof(f53,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f51,f27])).

fof(f51,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f30,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f30,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f198,plain,
    ( k1_relat_1(sK1) != k1_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f197,f35])).

fof(f35,plain,(
    k2_funct_1(sK0) != sK1 ),
    inference(cnf_transformation,[],[f23])).

fof(f197,plain,
    ( k2_funct_1(sK0) = sK1
    | k1_relat_1(sK1) != k1_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ spl3_1 ),
    inference(trivial_inequality_removal,[],[f195])).

fof(f195,plain,
    ( k1_funct_1(sK1,sK2(k2_funct_1(sK0),sK1)) != k1_funct_1(sK1,sK2(k2_funct_1(sK0),sK1))
    | k2_funct_1(sK0) = sK1
    | k1_relat_1(sK1) != k1_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ spl3_1 ),
    inference(superposition,[],[f41,f193])).

fof(f193,plain,
    ( k1_funct_1(sK1,sK2(k2_funct_1(sK0),sK1)) = k1_funct_1(k2_funct_1(sK0),sK2(k2_funct_1(sK0),sK1))
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f159,f158])).

fof(f158,plain,
    ( sK2(k2_funct_1(sK0),sK1) = k1_funct_1(sK0,k1_funct_1(sK1,sK2(k2_funct_1(sK0),sK1)))
    | ~ spl3_1 ),
    inference(resolution,[],[f157,f108])).

fof(f108,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(sK0,k1_funct_1(sK1,X0)) = X0 ) ),
    inference(duplicate_literal_removal,[],[f105])).

fof(f105,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(sK0,k1_funct_1(sK1,X0)) = X0 ) ),
    inference(resolution,[],[f59,f45])).

% (20766)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
fof(f45,plain,(
    ! [X3] :
      ( ~ r2_hidden(k1_funct_1(sK1,X3),k1_relat_1(sK0))
      | ~ r2_hidden(X3,k1_relat_1(sK1))
      | k1_funct_1(sK0,k1_funct_1(sK1,X3)) = X3 ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X3] :
      ( k1_funct_1(sK0,X2) = X3
      | k1_funct_1(sK1,X3) != X2
      | ~ r2_hidden(X3,k1_relat_1(sK1))
      | ~ r2_hidden(X2,k1_relat_1(sK0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f59,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK1,X0),k1_relat_1(sK0))
      | ~ r2_hidden(X0,k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f58,f28])).

fof(f58,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK1,X0),k1_relat_1(sK0))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f57,f29])).

fof(f57,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK1,X0),k1_relat_1(sK0))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f42,f31])).

fof(f31,plain,(
    k1_relat_1(sK0) = k2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

fof(f157,plain,
    ( r2_hidden(sK2(k2_funct_1(sK0),sK1),k1_relat_1(sK1))
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f156,f28])).

fof(f156,plain,
    ( r2_hidden(sK2(k2_funct_1(sK0),sK1),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f155,f29])).

fof(f155,plain,
    ( r2_hidden(sK2(k2_funct_1(sK0),sK1),k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f154,f35])).

fof(f154,plain,
    ( r2_hidden(sK2(k2_funct_1(sK0),sK1),k1_relat_1(sK1))
    | k2_funct_1(sK0) = sK1
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_1 ),
    inference(equality_resolution,[],[f101])).

fof(f101,plain,
    ( ! [X2] :
        ( k1_relat_1(sK1) != k1_relat_1(X2)
        | r2_hidden(sK2(k2_funct_1(sK0),X2),k1_relat_1(sK1))
        | k2_funct_1(sK0) = X2
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f100,f48])).

fof(f100,plain,
    ( ! [X2] :
        ( k1_relat_1(sK1) != k1_relat_1(X2)
        | r2_hidden(sK2(k2_funct_1(sK0),X2),k1_relat_1(sK1))
        | k2_funct_1(sK0) = X2
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(k2_funct_1(sK0)) )
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f82,f68])).

fof(f82,plain,(
    ! [X2] :
      ( k1_relat_1(sK1) != k1_relat_1(X2)
      | r2_hidden(sK2(k2_funct_1(sK0),X2),k1_relat_1(sK1))
      | k2_funct_1(sK0) = X2
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(k2_funct_1(sK0))
      | ~ v1_relat_1(k2_funct_1(sK0)) ) ),
    inference(superposition,[],[f40,f63])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k1_relat_1(X0)
      | r2_hidden(sK2(X0,X1),k1_relat_1(X0))
      | X0 = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
            & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X1) = k1_relat_1(X0) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

fof(f159,plain,
    ( k1_funct_1(sK1,sK2(k2_funct_1(sK0),sK1)) = k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,k1_funct_1(sK1,sK2(k2_funct_1(sK0),sK1))))
    | ~ spl3_1 ),
    inference(resolution,[],[f157,f111])).

fof(f111,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_relat_1(sK1))
      | k1_funct_1(sK1,X1) = k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,k1_funct_1(sK1,X1))) ) ),
    inference(subsumption_resolution,[],[f110,f26])).

fof(f110,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_relat_1(sK1))
      | k1_funct_1(sK1,X1) = k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,k1_funct_1(sK1,X1)))
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f109,f27])).

fof(f109,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_relat_1(sK1))
      | k1_funct_1(sK1,X1) = k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,k1_funct_1(sK1,X1)))
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f106,f30])).

fof(f106,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_relat_1(sK1))
      | k1_funct_1(sK1,X1) = k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,k1_funct_1(sK1,X1)))
      | ~ v2_funct_1(sK0)
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f59,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
      | X0 = X1
      | k1_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f77,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f76])).

fof(f76,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f75,f26])).

fof(f75,plain,
    ( ~ v1_relat_1(sK0)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f74,f27])).

fof(f74,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl3_1 ),
    inference(resolution,[],[f69,f37])).

fof(f37,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f69,plain,
    ( ~ v1_funct_1(k2_funct_1(sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f67])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:40:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (20763)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.49  % (20763)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f209,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f77,f204])).
% 0.21/0.49  fof(f204,plain,(
% 0.21/0.49    ~spl3_1),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f203])).
% 0.21/0.49  fof(f203,plain,(
% 0.21/0.49    $false | ~spl3_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f202,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    v1_relat_1(k2_funct_1(sK0))),
% 0.21/0.49    inference(subsumption_resolution,[],[f47,f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    v1_relat_1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    (k2_funct_1(sK0) != sK1 & ! [X2,X3] : (((k1_funct_1(sK0,X2) = X3 | k1_funct_1(sK1,X3) != X2) & (k1_funct_1(sK1,X3) = X2 | k1_funct_1(sK0,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(sK1)) | ~r2_hidden(X2,k1_relat_1(sK0))) & k2_relat_1(sK0) = k1_relat_1(sK1) & k1_relat_1(sK0) = k2_relat_1(sK1) & v2_funct_1(sK0) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22,f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & ! [X2,X3] : (((k1_funct_1(X0,X2) = X3 | k1_funct_1(X1,X3) != X2) & (k1_funct_1(X1,X3) = X2 | k1_funct_1(X0,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0))) & k1_relat_1(X1) = k2_relat_1(X0) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k2_funct_1(sK0) != X1 & ! [X3,X2] : (((k1_funct_1(sK0,X2) = X3 | k1_funct_1(X1,X3) != X2) & (k1_funct_1(X1,X3) = X2 | k1_funct_1(sK0,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(sK0))) & k1_relat_1(X1) = k2_relat_1(sK0) & k2_relat_1(X1) = k1_relat_1(sK0) & v2_funct_1(sK0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ? [X1] : (k2_funct_1(sK0) != X1 & ! [X3,X2] : (((k1_funct_1(sK0,X2) = X3 | k1_funct_1(X1,X3) != X2) & (k1_funct_1(X1,X3) = X2 | k1_funct_1(sK0,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(sK0))) & k1_relat_1(X1) = k2_relat_1(sK0) & k2_relat_1(X1) = k1_relat_1(sK0) & v2_funct_1(sK0) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(sK0) != sK1 & ! [X3,X2] : (((k1_funct_1(sK0,X2) = X3 | k1_funct_1(sK1,X3) != X2) & (k1_funct_1(sK1,X3) = X2 | k1_funct_1(sK0,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(sK1)) | ~r2_hidden(X2,k1_relat_1(sK0))) & k2_relat_1(sK0) = k1_relat_1(sK1) & k1_relat_1(sK0) = k2_relat_1(sK1) & v2_funct_1(sK0) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & ! [X2,X3] : (((k1_funct_1(X0,X2) = X3 | k1_funct_1(X1,X3) != X2) & (k1_funct_1(X1,X3) = X2 | k1_funct_1(X0,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0))) & k1_relat_1(X1) = k2_relat_1(X0) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & ! [X2,X3] : ((k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0))) & k1_relat_1(X1) = k2_relat_1(X0) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : ((k2_funct_1(X0) != X1 & (! [X2,X3] : ((k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2) | (~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0)))) & k1_relat_1(X1) = k2_relat_1(X0) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2,X3] : ((r2_hidden(X3,k1_relat_1(X1)) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2)) & k1_relat_1(X1) = k2_relat_1(X0) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.21/0.49    inference(negated_conjecture,[],[f6])).
% 0.21/0.49  fof(f6,conjecture,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2,X3] : ((r2_hidden(X3,k1_relat_1(X1)) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2)) & k1_relat_1(X1) = k2_relat_1(X0) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_1)).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    v1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0)),
% 0.21/0.49    inference(resolution,[],[f27,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    v1_funct_1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f202,plain,(
% 0.21/0.49    ~v1_relat_1(k2_funct_1(sK0)) | ~spl3_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f201,f68])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    v1_funct_1(k2_funct_1(sK0)) | ~spl3_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    spl3_1 <=> v1_funct_1(k2_funct_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.49  fof(f201,plain,(
% 0.21/0.49    ~v1_funct_1(k2_funct_1(sK0)) | ~v1_relat_1(k2_funct_1(sK0)) | ~spl3_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f200,f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    v1_relat_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f200,plain,(
% 0.21/0.49    ~v1_relat_1(sK1) | ~v1_funct_1(k2_funct_1(sK0)) | ~v1_relat_1(k2_funct_1(sK0)) | ~spl3_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f199,f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    v1_funct_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f199,plain,(
% 0.21/0.49    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(k2_funct_1(sK0)) | ~v1_relat_1(k2_funct_1(sK0)) | ~spl3_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f198,f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    k1_relat_1(sK1) = k1_relat_1(k2_funct_1(sK0))),
% 0.21/0.49    inference(forward_demodulation,[],[f54,f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    k2_relat_1(sK0) = k1_relat_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 0.21/0.49    inference(subsumption_resolution,[],[f53,f26])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f51,f27])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 0.21/0.49    inference(resolution,[],[f30,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    v2_funct_1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f198,plain,(
% 0.21/0.49    k1_relat_1(sK1) != k1_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(k2_funct_1(sK0)) | ~v1_relat_1(k2_funct_1(sK0)) | ~spl3_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f197,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    k2_funct_1(sK0) != sK1),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f197,plain,(
% 0.21/0.49    k2_funct_1(sK0) = sK1 | k1_relat_1(sK1) != k1_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(k2_funct_1(sK0)) | ~v1_relat_1(k2_funct_1(sK0)) | ~spl3_1),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f195])).
% 0.21/0.49  fof(f195,plain,(
% 0.21/0.49    k1_funct_1(sK1,sK2(k2_funct_1(sK0),sK1)) != k1_funct_1(sK1,sK2(k2_funct_1(sK0),sK1)) | k2_funct_1(sK0) = sK1 | k1_relat_1(sK1) != k1_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(k2_funct_1(sK0)) | ~v1_relat_1(k2_funct_1(sK0)) | ~spl3_1),
% 0.21/0.49    inference(superposition,[],[f41,f193])).
% 0.21/0.49  fof(f193,plain,(
% 0.21/0.49    k1_funct_1(sK1,sK2(k2_funct_1(sK0),sK1)) = k1_funct_1(k2_funct_1(sK0),sK2(k2_funct_1(sK0),sK1)) | ~spl3_1),
% 0.21/0.49    inference(forward_demodulation,[],[f159,f158])).
% 0.21/0.49  fof(f158,plain,(
% 0.21/0.49    sK2(k2_funct_1(sK0),sK1) = k1_funct_1(sK0,k1_funct_1(sK1,sK2(k2_funct_1(sK0),sK1))) | ~spl3_1),
% 0.21/0.49    inference(resolution,[],[f157,f108])).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK0,k1_funct_1(sK1,X0)) = X0) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f105])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | ~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK0,k1_funct_1(sK1,X0)) = X0) )),
% 0.21/0.49    inference(resolution,[],[f59,f45])).
% 0.21/0.49  % (20766)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X3] : (~r2_hidden(k1_funct_1(sK1,X3),k1_relat_1(sK0)) | ~r2_hidden(X3,k1_relat_1(sK1)) | k1_funct_1(sK0,k1_funct_1(sK1,X3)) = X3) )),
% 0.21/0.49    inference(equality_resolution,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X2,X3] : (k1_funct_1(sK0,X2) = X3 | k1_funct_1(sK1,X3) != X2 | ~r2_hidden(X3,k1_relat_1(sK1)) | ~r2_hidden(X2,k1_relat_1(sK0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(k1_funct_1(sK1,X0),k1_relat_1(sK0)) | ~r2_hidden(X0,k1_relat_1(sK1))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f58,f28])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(k1_funct_1(sK1,X0),k1_relat_1(sK0)) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f57,f29])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(k1_funct_1(sK1,X0),k1_relat_1(sK0)) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 0.21/0.49    inference(superposition,[],[f42,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    k1_relat_1(sK0) = k2_relat_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).
% 0.21/0.49  fof(f157,plain,(
% 0.21/0.49    r2_hidden(sK2(k2_funct_1(sK0),sK1),k1_relat_1(sK1)) | ~spl3_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f156,f28])).
% 0.21/0.49  fof(f156,plain,(
% 0.21/0.49    r2_hidden(sK2(k2_funct_1(sK0),sK1),k1_relat_1(sK1)) | ~v1_relat_1(sK1) | ~spl3_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f155,f29])).
% 0.21/0.49  fof(f155,plain,(
% 0.21/0.49    r2_hidden(sK2(k2_funct_1(sK0),sK1),k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl3_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f154,f35])).
% 0.21/0.49  fof(f154,plain,(
% 0.21/0.49    r2_hidden(sK2(k2_funct_1(sK0),sK1),k1_relat_1(sK1)) | k2_funct_1(sK0) = sK1 | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl3_1),
% 0.21/0.49    inference(equality_resolution,[],[f101])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    ( ! [X2] : (k1_relat_1(sK1) != k1_relat_1(X2) | r2_hidden(sK2(k2_funct_1(sK0),X2),k1_relat_1(sK1)) | k2_funct_1(sK0) = X2 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) ) | ~spl3_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f100,f48])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    ( ! [X2] : (k1_relat_1(sK1) != k1_relat_1(X2) | r2_hidden(sK2(k2_funct_1(sK0),X2),k1_relat_1(sK1)) | k2_funct_1(sK0) = X2 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(k2_funct_1(sK0))) ) | ~spl3_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f82,f68])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ( ! [X2] : (k1_relat_1(sK1) != k1_relat_1(X2) | r2_hidden(sK2(k2_funct_1(sK0),X2),k1_relat_1(sK1)) | k2_funct_1(sK0) = X2 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(k2_funct_1(sK0)) | ~v1_relat_1(k2_funct_1(sK0))) )),
% 0.21/0.49    inference(superposition,[],[f40,f63])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_relat_1(X1) != k1_relat_1(X0) | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) | X0 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X1) != k1_relat_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X1) = k1_relat_1(X0)) => X0 = X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).
% 0.21/0.49  fof(f159,plain,(
% 0.21/0.49    k1_funct_1(sK1,sK2(k2_funct_1(sK0),sK1)) = k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,k1_funct_1(sK1,sK2(k2_funct_1(sK0),sK1)))) | ~spl3_1),
% 0.21/0.49    inference(resolution,[],[f157,f111])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK1)) | k1_funct_1(sK1,X1) = k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,k1_funct_1(sK1,X1)))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f110,f26])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK1)) | k1_funct_1(sK1,X1) = k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,k1_funct_1(sK1,X1))) | ~v1_relat_1(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f109,f27])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK1)) | k1_funct_1(sK1,X1) = k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,k1_funct_1(sK1,X1))) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f106,f30])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK1)) | k1_funct_1(sK1,X1) = k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,k1_funct_1(sK1,X1))) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f59,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | (~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) | X0 = X1 | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    spl3_1),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f76])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    $false | spl3_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f75,f26])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    ~v1_relat_1(sK0) | spl3_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f74,f27])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl3_1),
% 0.21/0.49    inference(resolution,[],[f69,f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ~v1_funct_1(k2_funct_1(sK0)) | spl3_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f67])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (20763)------------------------------
% 0.21/0.49  % (20763)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (20763)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (20763)Memory used [KB]: 10746
% 0.21/0.49  % (20763)Time elapsed: 0.072 s
% 0.21/0.49  % (20763)------------------------------
% 0.21/0.49  % (20763)------------------------------
% 0.21/0.49  % (20761)Success in time 0.134 s
%------------------------------------------------------------------------------
