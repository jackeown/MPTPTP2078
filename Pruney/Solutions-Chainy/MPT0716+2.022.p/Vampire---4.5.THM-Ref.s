%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 543 expanded)
%              Number of leaves         :   11 ( 169 expanded)
%              Depth                    :   21
%              Number of atoms          :  243 (4234 expanded)
%              Number of equality atoms :   18 (  75 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f462,plain,(
    $false ),
    inference(resolution,[],[f453,f418])).

fof(f418,plain,(
    r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) ),
    inference(resolution,[],[f411,f314])).

fof(f314,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK0,X0),k10_relat_1(sK0,X0)) ),
    inference(resolution,[],[f313,f27])).

fof(f27,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
      | ~ r1_tarski(sK2,k1_relat_1(sK0))
      | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) )
    & ( ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
        & r1_tarski(sK2,k1_relat_1(sK0)) )
      | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) )
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f25,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  | ~ r1_tarski(X2,k1_relat_1(X0))
                  | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
                & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                    & r1_tarski(X2,k1_relat_1(X0)) )
                  | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1))
                | ~ r1_tarski(X2,k1_relat_1(sK0))
                | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))) )
              & ( ( r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(sK0)) )
                | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(sK0))
              | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))) )
            & ( ( r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(sK0)) )
              | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))) ) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1))
            | ~ r1_tarski(X2,k1_relat_1(sK0))
            | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1))) )
          & ( ( r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1))
              & r1_tarski(X2,k1_relat_1(sK0)) )
            | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1))) ) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1))
          | ~ r1_tarski(X2,k1_relat_1(sK0))
          | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1))) )
        & ( ( r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1))
            & r1_tarski(X2,k1_relat_1(sK0)) )
          | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1))) ) )
   => ( ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
        | ~ r1_tarski(sK2,k1_relat_1(sK0))
        | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) )
      & ( ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
          & r1_tarski(sK2,k1_relat_1(sK0)) )
        | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                | ~ r1_tarski(X2,k1_relat_1(X0))
                | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
              & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) )
                | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

% (15206)Refutation not found, incomplete strategy% (15206)------------------------------
% (15206)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15206)Termination reason: Refutation not found, incomplete strategy

% (15206)Memory used [KB]: 10490
% (15206)Time elapsed: 0.151 s
% (15206)------------------------------
% (15206)------------------------------
% (15218)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% (15209)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% (15203)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                | ~ r1_tarski(X2,k1_relat_1(X0))
                | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
              & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) )
                | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <~> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <~> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) )
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
           => ! [X2] :
                ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
              <=> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <=> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_1)).

fof(f313,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK0)
      | r1_tarski(k10_relat_1(sK0,X0),k10_relat_1(sK0,X0)) ) ),
    inference(resolution,[],[f312,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f312,plain,(
    ! [X0] :
      ( ~ r1_tarski(k10_relat_1(sK0,X0),k1_relat_1(sK0))
      | r1_tarski(k10_relat_1(sK0,X0),k10_relat_1(sK0,X0)) ) ),
    inference(resolution,[],[f311,f27])).

fof(f311,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK0)
      | r1_tarski(k10_relat_1(sK0,X0),k10_relat_1(sK0,X0))
      | ~ r1_tarski(k10_relat_1(sK0,X0),k1_relat_1(sK0)) ) ),
    inference(resolution,[],[f131,f28])).

fof(f28,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f131,plain,(
    ! [X2] :
      ( ~ v1_funct_1(sK0)
      | ~ r1_tarski(k10_relat_1(sK0,X2),k1_relat_1(sK0))
      | r1_tarski(k10_relat_1(sK0,X2),k10_relat_1(sK0,X2))
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f86,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k9_relat_1(sK0,X0),X1)
      | r1_tarski(X0,k10_relat_1(sK0,X1))
      | ~ r1_tarski(X0,k1_relat_1(sK0)) ) ),
    inference(resolution,[],[f81,f27])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK0)
      | ~ r1_tarski(X0,k1_relat_1(sK0))
      | r1_tarski(X0,k10_relat_1(sK0,X1))
      | ~ r1_tarski(k9_relat_1(sK0,X0),X1) ) ),
    inference(resolution,[],[f40,f28])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

fof(f411,plain,(
    ! [X0] :
      ( ~ r1_tarski(k10_relat_1(sK0,k1_relat_1(sK1)),X0)
      | r1_tarski(sK2,X0) ) ),
    inference(superposition,[],[f39,f410])).

fof(f410,plain,(
    k10_relat_1(sK0,k1_relat_1(sK1)) = k2_xboole_0(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) ),
    inference(duplicate_literal_removal,[],[f409])).

fof(f409,plain,
    ( k10_relat_1(sK0,k1_relat_1(sK1)) = k2_xboole_0(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | k10_relat_1(sK0,k1_relat_1(sK1)) = k2_xboole_0(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) ),
    inference(resolution,[],[f137,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f137,plain,
    ( r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | k10_relat_1(sK0,k1_relat_1(sK1)) = k2_xboole_0(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) ),
    inference(resolution,[],[f133,f54])).

fof(f54,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0))
    | k10_relat_1(sK0,k1_relat_1(sK1)) = k2_xboole_0(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) ),
    inference(backward_demodulation,[],[f42,f52])).

fof(f52,plain,(
    k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1)) ),
    inference(resolution,[],[f49,f29])).

fof(f29,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(sK0,X0)) = k10_relat_1(sK0,k1_relat_1(X0)) ) ),
    inference(resolution,[],[f34,f27])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f42,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0))
    | k1_relat_1(k5_relat_1(sK0,sK1)) = k2_xboole_0(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(resolution,[],[f31,f36])).

fof(f31,plain,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | r1_tarski(sK2,k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f133,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK0))
    | r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) ),
    inference(duplicate_literal_removal,[],[f129])).

% (15213)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
fof(f129,plain,
    ( r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | ~ r1_tarski(sK2,k1_relat_1(sK0))
    | r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) ),
    inference(resolution,[],[f86,f56])).

fof(f56,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) ),
    inference(backward_demodulation,[],[f32,f52])).

fof(f32,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f453,plain,(
    ~ r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) ),
    inference(resolution,[],[f452,f423])).

fof(f423,plain,
    ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) ),
    inference(resolution,[],[f421,f57])).

fof(f57,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK0))
    | ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) ),
    inference(backward_demodulation,[],[f33,f52])).

fof(f33,plain,
    ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ r1_tarski(sK2,k1_relat_1(sK0))
    | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f421,plain,(
    r1_tarski(sK2,k1_relat_1(sK0)) ),
    inference(resolution,[],[f420,f27])).

fof(f420,plain,
    ( ~ v1_relat_1(sK0)
    | r1_tarski(sK2,k1_relat_1(sK0)) ),
    inference(resolution,[],[f411,f35])).

fof(f452,plain,(
    r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) ),
    inference(resolution,[],[f451,f27])).

fof(f451,plain,
    ( ~ v1_relat_1(sK0)
    | r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) ),
    inference(resolution,[],[f450,f28])).

fof(f450,plain,
    ( ~ v1_funct_1(sK0)
    | r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f412,f37])).

fof(f412,plain,(
    ! [X1] :
      ( ~ r1_tarski(k9_relat_1(sK0,k10_relat_1(sK0,k1_relat_1(sK1))),X1)
      | r1_tarski(k9_relat_1(sK0,sK2),X1) ) ),
    inference(superposition,[],[f71,f410])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k9_relat_1(sK0,k2_xboole_0(X0,X1)),X2)
      | r1_tarski(k9_relat_1(sK0,X0),X2) ) ),
    inference(superposition,[],[f39,f69])).

fof(f69,plain,(
    ! [X0,X1] : k9_relat_1(sK0,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(sK0,X0),k9_relat_1(sK0,X1)) ),
    inference(resolution,[],[f38,f27])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t153_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:05:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (15204)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.52  % (15211)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.52  % (15212)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.53  % (15205)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.53  % (15223)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.53  % (15222)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.54  % (15211)Refutation not found, incomplete strategy% (15211)------------------------------
% 0.21/0.54  % (15211)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (15206)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.54  % (15210)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (15211)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (15211)Memory used [KB]: 10746
% 0.21/0.54  % (15211)Time elapsed: 0.087 s
% 0.21/0.54  % (15211)------------------------------
% 0.21/0.54  % (15211)------------------------------
% 0.21/0.55  % (15228)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.55  % (15228)Refutation not found, incomplete strategy% (15228)------------------------------
% 0.21/0.55  % (15228)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (15228)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (15228)Memory used [KB]: 10618
% 0.21/0.55  % (15228)Time elapsed: 0.129 s
% 0.21/0.55  % (15228)------------------------------
% 0.21/0.55  % (15228)------------------------------
% 0.21/0.55  % (15226)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.55  % (15224)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.56  % (15221)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.56  % (15212)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f462,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(resolution,[],[f453,f418])).
% 0.21/0.56  fof(f418,plain,(
% 0.21/0.56    r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))),
% 0.21/0.56    inference(resolution,[],[f411,f314])).
% 0.21/0.56  fof(f314,plain,(
% 0.21/0.56    ( ! [X0] : (r1_tarski(k10_relat_1(sK0,X0),k10_relat_1(sK0,X0))) )),
% 0.21/0.56    inference(resolution,[],[f313,f27])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    v1_relat_1(sK0)),
% 0.21/0.56    inference(cnf_transformation,[],[f26])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    (((~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(sK0)) | ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))) & ((r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) & r1_tarski(sK2,k1_relat_1(sK0))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))))) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f25,f24,f23])).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(sK0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1)))) & ((r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(sK0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    ? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(sK0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1)))) & ((r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(sK0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : ((~r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1)) | ~r1_tarski(X2,k1_relat_1(sK0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1)))) & ((r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1)) & r1_tarski(X2,k1_relat_1(sK0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1))))) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    ? [X2] : ((~r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1)) | ~r1_tarski(X2,k1_relat_1(sK0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1)))) & ((r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1)) & r1_tarski(X2,k1_relat_1(sK0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1))))) => ((~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(sK0)) | ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))) & ((r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) & r1_tarski(sK2,k1_relat_1(sK0))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.56    inference(flattening,[],[f21])).
% 0.21/0.56  % (15206)Refutation not found, incomplete strategy% (15206)------------------------------
% 0.21/0.56  % (15206)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (15206)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (15206)Memory used [KB]: 10490
% 0.21/0.56  % (15206)Time elapsed: 0.151 s
% 0.21/0.56  % (15206)------------------------------
% 0.21/0.56  % (15206)------------------------------
% 0.21/0.57  % (15218)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.57  % (15209)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 1.64/0.57  % (15203)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 1.64/0.57  fof(f21,plain,(
% 1.64/0.57    ? [X0] : (? [X1] : (? [X2] : (((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.64/0.57    inference(nnf_transformation,[],[f11])).
% 1.64/0.57  fof(f11,plain,(
% 1.64/0.57    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.64/0.57    inference(flattening,[],[f10])).
% 1.64/0.57  fof(f10,plain,(
% 1.64/0.57    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.64/0.57    inference(ennf_transformation,[],[f9])).
% 1.64/0.57  fof(f9,negated_conjecture,(
% 1.64/0.57    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 1.64/0.57    inference(negated_conjecture,[],[f8])).
% 1.64/0.57  fof(f8,conjecture,(
% 1.64/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 1.64/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_1)).
% 1.64/0.57  fof(f313,plain,(
% 1.64/0.57    ( ! [X0] : (~v1_relat_1(sK0) | r1_tarski(k10_relat_1(sK0,X0),k10_relat_1(sK0,X0))) )),
% 1.64/0.57    inference(resolution,[],[f312,f35])).
% 1.64/0.57  fof(f35,plain,(
% 1.64/0.57    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f13])).
% 1.64/0.57  fof(f13,plain,(
% 1.64/0.57    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.64/0.57    inference(ennf_transformation,[],[f4])).
% 1.64/0.57  fof(f4,axiom,(
% 1.64/0.57    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 1.64/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 1.64/0.57  fof(f312,plain,(
% 1.64/0.57    ( ! [X0] : (~r1_tarski(k10_relat_1(sK0,X0),k1_relat_1(sK0)) | r1_tarski(k10_relat_1(sK0,X0),k10_relat_1(sK0,X0))) )),
% 1.64/0.57    inference(resolution,[],[f311,f27])).
% 1.64/0.57  fof(f311,plain,(
% 1.64/0.57    ( ! [X0] : (~v1_relat_1(sK0) | r1_tarski(k10_relat_1(sK0,X0),k10_relat_1(sK0,X0)) | ~r1_tarski(k10_relat_1(sK0,X0),k1_relat_1(sK0))) )),
% 1.64/0.57    inference(resolution,[],[f131,f28])).
% 1.64/0.57  fof(f28,plain,(
% 1.64/0.57    v1_funct_1(sK0)),
% 1.64/0.57    inference(cnf_transformation,[],[f26])).
% 1.64/0.57  fof(f131,plain,(
% 1.64/0.57    ( ! [X2] : (~v1_funct_1(sK0) | ~r1_tarski(k10_relat_1(sK0,X2),k1_relat_1(sK0)) | r1_tarski(k10_relat_1(sK0,X2),k10_relat_1(sK0,X2)) | ~v1_relat_1(sK0)) )),
% 1.64/0.57    inference(resolution,[],[f86,f37])).
% 1.64/0.57  fof(f37,plain,(
% 1.64/0.57    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f16])).
% 1.64/0.57  fof(f16,plain,(
% 1.64/0.57    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.64/0.57    inference(flattening,[],[f15])).
% 1.64/0.57  fof(f15,plain,(
% 1.64/0.57    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.64/0.57    inference(ennf_transformation,[],[f6])).
% 1.64/0.57  fof(f6,axiom,(
% 1.64/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 1.64/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).
% 1.64/0.57  fof(f86,plain,(
% 1.64/0.57    ( ! [X0,X1] : (~r1_tarski(k9_relat_1(sK0,X0),X1) | r1_tarski(X0,k10_relat_1(sK0,X1)) | ~r1_tarski(X0,k1_relat_1(sK0))) )),
% 1.64/0.57    inference(resolution,[],[f81,f27])).
% 1.64/0.57  fof(f81,plain,(
% 1.64/0.57    ( ! [X0,X1] : (~v1_relat_1(sK0) | ~r1_tarski(X0,k1_relat_1(sK0)) | r1_tarski(X0,k10_relat_1(sK0,X1)) | ~r1_tarski(k9_relat_1(sK0,X0),X1)) )),
% 1.64/0.57    inference(resolution,[],[f40,f28])).
% 1.64/0.57  fof(f40,plain,(
% 1.64/0.57    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | r1_tarski(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f20])).
% 1.64/0.57  fof(f20,plain,(
% 1.64/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.64/0.57    inference(flattening,[],[f19])).
% 1.64/0.57  fof(f19,plain,(
% 1.64/0.57    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.64/0.57    inference(ennf_transformation,[],[f7])).
% 1.64/0.57  fof(f7,axiom,(
% 1.64/0.57    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 1.64/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).
% 1.64/0.57  fof(f411,plain,(
% 1.64/0.57    ( ! [X0] : (~r1_tarski(k10_relat_1(sK0,k1_relat_1(sK1)),X0) | r1_tarski(sK2,X0)) )),
% 1.64/0.57    inference(superposition,[],[f39,f410])).
% 1.64/0.57  fof(f410,plain,(
% 1.64/0.57    k10_relat_1(sK0,k1_relat_1(sK1)) = k2_xboole_0(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))),
% 1.64/0.57    inference(duplicate_literal_removal,[],[f409])).
% 1.64/0.57  fof(f409,plain,(
% 1.64/0.57    k10_relat_1(sK0,k1_relat_1(sK1)) = k2_xboole_0(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) | k10_relat_1(sK0,k1_relat_1(sK1)) = k2_xboole_0(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))),
% 1.64/0.57    inference(resolution,[],[f137,f36])).
% 1.64/0.57  fof(f36,plain,(
% 1.64/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.64/0.57    inference(cnf_transformation,[],[f14])).
% 1.64/0.57  fof(f14,plain,(
% 1.64/0.57    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.64/0.57    inference(ennf_transformation,[],[f2])).
% 1.64/0.57  fof(f2,axiom,(
% 1.64/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.64/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.64/0.57  fof(f137,plain,(
% 1.64/0.57    r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) | k10_relat_1(sK0,k1_relat_1(sK1)) = k2_xboole_0(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))),
% 1.64/0.57    inference(resolution,[],[f133,f54])).
% 1.64/0.57  fof(f54,plain,(
% 1.64/0.57    r1_tarski(sK2,k1_relat_1(sK0)) | k10_relat_1(sK0,k1_relat_1(sK1)) = k2_xboole_0(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))),
% 1.64/0.57    inference(backward_demodulation,[],[f42,f52])).
% 1.64/0.57  fof(f52,plain,(
% 1.64/0.57    k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1))),
% 1.64/0.57    inference(resolution,[],[f49,f29])).
% 1.64/0.57  fof(f29,plain,(
% 1.64/0.57    v1_relat_1(sK1)),
% 1.64/0.57    inference(cnf_transformation,[],[f26])).
% 1.64/0.57  fof(f49,plain,(
% 1.64/0.57    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(sK0,X0)) = k10_relat_1(sK0,k1_relat_1(X0))) )),
% 1.64/0.57    inference(resolution,[],[f34,f27])).
% 1.64/0.57  fof(f34,plain,(
% 1.64/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 1.64/0.57    inference(cnf_transformation,[],[f12])).
% 1.64/0.57  fof(f12,plain,(
% 1.64/0.57    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.64/0.57    inference(ennf_transformation,[],[f5])).
% 1.64/0.57  fof(f5,axiom,(
% 1.64/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 1.64/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 1.64/0.57  fof(f42,plain,(
% 1.64/0.57    r1_tarski(sK2,k1_relat_1(sK0)) | k1_relat_1(k5_relat_1(sK0,sK1)) = k2_xboole_0(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 1.64/0.57    inference(resolution,[],[f31,f36])).
% 1.64/0.57  fof(f31,plain,(
% 1.64/0.57    r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) | r1_tarski(sK2,k1_relat_1(sK0))),
% 1.64/0.57    inference(cnf_transformation,[],[f26])).
% 1.64/0.57  fof(f133,plain,(
% 1.64/0.57    ~r1_tarski(sK2,k1_relat_1(sK0)) | r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))),
% 1.64/0.57    inference(duplicate_literal_removal,[],[f129])).
% 1.64/0.57  % (15213)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 1.64/0.57  fof(f129,plain,(
% 1.64/0.57    r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) | ~r1_tarski(sK2,k1_relat_1(sK0)) | r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))),
% 1.64/0.57    inference(resolution,[],[f86,f56])).
% 1.64/0.57  fof(f56,plain,(
% 1.64/0.57    r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))),
% 1.64/0.57    inference(backward_demodulation,[],[f32,f52])).
% 1.64/0.57  fof(f32,plain,(
% 1.64/0.57    r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 1.64/0.57    inference(cnf_transformation,[],[f26])).
% 1.64/0.57  fof(f39,plain,(
% 1.64/0.57    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f18])).
% 1.64/0.57  fof(f18,plain,(
% 1.64/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.64/0.57    inference(ennf_transformation,[],[f1])).
% 1.64/0.57  fof(f1,axiom,(
% 1.64/0.57    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.64/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.64/0.57  fof(f453,plain,(
% 1.64/0.57    ~r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))),
% 1.64/0.57    inference(resolution,[],[f452,f423])).
% 1.64/0.57  fof(f423,plain,(
% 1.64/0.57    ~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))),
% 1.64/0.57    inference(resolution,[],[f421,f57])).
% 1.64/0.57  fof(f57,plain,(
% 1.64/0.57    ~r1_tarski(sK2,k1_relat_1(sK0)) | ~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))),
% 1.64/0.57    inference(backward_demodulation,[],[f33,f52])).
% 1.64/0.57  fof(f33,plain,(
% 1.64/0.57    ~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(sK0)) | ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 1.64/0.57    inference(cnf_transformation,[],[f26])).
% 1.64/0.57  fof(f421,plain,(
% 1.64/0.57    r1_tarski(sK2,k1_relat_1(sK0))),
% 1.64/0.57    inference(resolution,[],[f420,f27])).
% 1.64/0.57  fof(f420,plain,(
% 1.64/0.57    ~v1_relat_1(sK0) | r1_tarski(sK2,k1_relat_1(sK0))),
% 1.64/0.57    inference(resolution,[],[f411,f35])).
% 1.64/0.57  fof(f452,plain,(
% 1.64/0.57    r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))),
% 1.64/0.57    inference(resolution,[],[f451,f27])).
% 1.64/0.57  fof(f451,plain,(
% 1.64/0.57    ~v1_relat_1(sK0) | r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))),
% 1.64/0.57    inference(resolution,[],[f450,f28])).
% 1.64/0.57  fof(f450,plain,(
% 1.64/0.57    ~v1_funct_1(sK0) | r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~v1_relat_1(sK0)),
% 1.64/0.57    inference(resolution,[],[f412,f37])).
% 1.64/0.57  fof(f412,plain,(
% 1.64/0.57    ( ! [X1] : (~r1_tarski(k9_relat_1(sK0,k10_relat_1(sK0,k1_relat_1(sK1))),X1) | r1_tarski(k9_relat_1(sK0,sK2),X1)) )),
% 1.64/0.57    inference(superposition,[],[f71,f410])).
% 1.64/0.57  fof(f71,plain,(
% 1.64/0.57    ( ! [X2,X0,X1] : (~r1_tarski(k9_relat_1(sK0,k2_xboole_0(X0,X1)),X2) | r1_tarski(k9_relat_1(sK0,X0),X2)) )),
% 1.64/0.57    inference(superposition,[],[f39,f69])).
% 1.64/0.57  fof(f69,plain,(
% 1.64/0.57    ( ! [X0,X1] : (k9_relat_1(sK0,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(sK0,X0),k9_relat_1(sK0,X1))) )),
% 1.64/0.57    inference(resolution,[],[f38,f27])).
% 1.64/0.57  fof(f38,plain,(
% 1.64/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) )),
% 1.64/0.57    inference(cnf_transformation,[],[f17])).
% 1.64/0.57  fof(f17,plain,(
% 1.64/0.57    ! [X0,X1,X2] : (k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.64/0.57    inference(ennf_transformation,[],[f3])).
% 1.64/0.57  fof(f3,axiom,(
% 1.64/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))),
% 1.64/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t153_relat_1)).
% 1.64/0.57  % SZS output end Proof for theBenchmark
% 1.64/0.57  % (15212)------------------------------
% 1.64/0.57  % (15212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.57  % (15212)Termination reason: Refutation
% 1.64/0.57  
% 1.64/0.57  % (15212)Memory used [KB]: 2302
% 1.64/0.57  % (15212)Time elapsed: 0.107 s
% 1.64/0.57  % (15212)------------------------------
% 1.64/0.57  % (15212)------------------------------
% 1.64/0.57  % (15200)Success in time 0.21 s
%------------------------------------------------------------------------------
