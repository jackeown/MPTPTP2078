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
% DateTime   : Thu Dec  3 12:52:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 289 expanded)
%              Number of leaves         :    5 (  57 expanded)
%              Depth                    :   26
%              Number of atoms          :  231 (1877 expanded)
%              Number of equality atoms :    3 (  18 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f60,plain,(
    $false ),
    inference(resolution,[],[f59,f21])).

fof(f21,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f59,plain,(
    ~ v1_relat_1(k6_relat_1(sK1)) ),
    inference(resolution,[],[f58,f22])).

fof(f22,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f58,plain,
    ( ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1)) ),
    inference(duplicate_literal_removal,[],[f57])).

fof(f57,plain,
    ( ~ v1_relat_1(k6_relat_1(sK1))
    | ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | ~ v1_funct_1(k6_relat_1(sK1)) ),
    inference(resolution,[],[f56,f49])).

fof(f49,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | ~ v1_funct_1(k6_relat_1(sK1)) ),
    inference(duplicate_literal_removal,[],[f48])).

fof(f48,plain,
    ( ~ v1_relat_1(k6_relat_1(sK1))
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(k6_relat_1(sK1))
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1)) ),
    inference(resolution,[],[f44,f40])).

fof(f40,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1)) ),
    inference(global_subsumption,[],[f17,f16,f39])).

fof(f39,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1)) ),
    inference(duplicate_literal_removal,[],[f38])).

fof(f38,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | ~ r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    inference(forward_demodulation,[],[f37,f23])).

fof(f23,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f37,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(k6_relat_1(sK1)))
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | ~ r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    inference(duplicate_literal_removal,[],[f34])).

fof(f34,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(k6_relat_1(sK1)))
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    inference(resolution,[],[f27,f20])).

fof(f20,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))))
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
      | ~ r2_hidden(sK0,k1_relat_1(sK2))
      | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1)))) )
    & ( ( r2_hidden(k1_funct_1(sK2,sK0),sK1)
        & r2_hidden(sK0,k1_relat_1(sK2)) )
      | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1)))) )
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) )
        & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
          | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) )
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
        | ~ r2_hidden(sK0,k1_relat_1(sK2))
        | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1)))) )
      & ( ( r2_hidden(k1_funct_1(sK2,sK0),sK1)
          & r2_hidden(sK0,k1_relat_1(sK2)) )
        | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1)))) )
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) )
      & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) )
        | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) )
      & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) )
        | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <~> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <~> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
        <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_1)).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).

fof(f16,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f17,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f44,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | ~ v1_relat_1(k6_relat_1(sK1))
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(k6_relat_1(sK1)) ),
    inference(resolution,[],[f43,f19])).

fof(f19,plain,
    ( r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))))
    | r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f43,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))))
    | ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | ~ r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(global_subsumption,[],[f17,f16,f42])).

fof(f42,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(duplicate_literal_removal,[],[f41])).

fof(f41,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1)) ),
    inference(resolution,[],[f40,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ r2_hidden(X2,k1_relat_1(k5_relat_1(X1,k6_relat_1(X0))))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f26,f23])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f56,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | ~ v1_funct_1(k6_relat_1(sK1)) ),
    inference(global_subsumption,[],[f17,f16,f55])).

fof(f55,plain,
    ( ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(duplicate_literal_removal,[],[f54])).

fof(f54,plain,
    ( ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1)) ),
    inference(resolution,[],[f51,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f51,plain,
    ( r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))))
    | ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1)) ),
    inference(resolution,[],[f49,f18])).

fof(f18,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1)))) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:45:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.43  % (30817)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.43  % (30816)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.43  % (30823)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.21/0.43  % (30816)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f60,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(resolution,[],[f59,f21])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.43  fof(f59,plain,(
% 0.21/0.43    ~v1_relat_1(k6_relat_1(sK1))),
% 0.21/0.43    inference(resolution,[],[f58,f22])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f2])).
% 0.21/0.43  fof(f58,plain,(
% 0.21/0.43    ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1))),
% 0.21/0.43    inference(duplicate_literal_removal,[],[f57])).
% 0.21/0.43  fof(f57,plain,(
% 0.21/0.43    ~v1_relat_1(k6_relat_1(sK1)) | ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1)) | ~v1_funct_1(k6_relat_1(sK1))),
% 0.21/0.43    inference(resolution,[],[f56,f49])).
% 0.21/0.43  fof(f49,plain,(
% 0.21/0.43    ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_relat_1(k6_relat_1(sK1)) | ~v1_funct_1(k6_relat_1(sK1))),
% 0.21/0.43    inference(duplicate_literal_removal,[],[f48])).
% 0.21/0.43  fof(f48,plain,(
% 0.21/0.43    ~v1_relat_1(k6_relat_1(sK1)) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(k6_relat_1(sK1)) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1))),
% 0.21/0.43    inference(resolution,[],[f44,f40])).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1))),
% 0.21/0.43    inference(global_subsumption,[],[f17,f16,f39])).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1))),
% 0.21/0.43    inference(duplicate_literal_removal,[],[f38])).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1)) | ~r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.21/0.43    inference(forward_demodulation,[],[f37,f23])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    ~r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(k6_relat_1(sK1))) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1)) | ~r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.21/0.43    inference(duplicate_literal_removal,[],[f34])).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    ~r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(k6_relat_1(sK1))) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1)) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.21/0.43    inference(resolution,[],[f27,f20])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1)))) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    (~r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))))) & ((r2_hidden(k1_funct_1(sK2,sK0),sK1) & r2_hidden(sK0,k1_relat_1(sK2))) | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))))) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))) & v1_funct_1(X2) & v1_relat_1(X2)) => ((~r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))))) & ((r2_hidden(k1_funct_1(sK2,sK0),sK1) & r2_hidden(sK0,k1_relat_1(sK2))) | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))))) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.43    inference(flattening,[],[f10])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ? [X0,X1,X2] : ((((~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))))) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.43    inference(nnf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,plain,(
% 0.21/0.43    ? [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <~> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.43    inference(flattening,[],[f6])).
% 0.21/0.43  fof(f6,plain,(
% 0.21/0.43    ? [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <~> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.21/0.43    inference(ennf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.43    inference(negated_conjecture,[],[f4])).
% 0.21/0.43  fof(f4,conjecture,(
% 0.21/0.43    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_1)).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ! [X0,X1] : (! [X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(flattening,[],[f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ! [X0,X1] : (! [X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | (~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2)))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(nnf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(flattening,[],[f8])).
% 0.21/0.43  fof(f8,plain,(
% 0.21/0.43    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.43    inference(ennf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))))))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    v1_relat_1(sK2)),
% 0.21/0.43    inference(cnf_transformation,[],[f13])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    v1_funct_1(sK2)),
% 0.21/0.43    inference(cnf_transformation,[],[f13])).
% 0.21/0.43  fof(f44,plain,(
% 0.21/0.43    r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~v1_relat_1(k6_relat_1(sK1)) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(k6_relat_1(sK1))),
% 0.21/0.43    inference(resolution,[],[f43,f19])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1)))) | r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f13])).
% 0.21/0.43  fof(f43,plain,(
% 0.21/0.43    ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1)))) | ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1)) | ~r2_hidden(sK0,k1_relat_1(sK2))),
% 0.21/0.43    inference(global_subsumption,[],[f17,f16,f42])).
% 0.21/0.43  fof(f42,plain,(
% 0.21/0.43    ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1)) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1)))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.21/0.43    inference(duplicate_literal_removal,[],[f41])).
% 0.21/0.43  fof(f41,plain,(
% 0.21/0.43    ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1)) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1)))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1))),
% 0.21/0.43    inference(resolution,[],[f40,f32])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(k5_relat_1(X1,k6_relat_1(X0)))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.43    inference(superposition,[],[f26,f23])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f56,plain,(
% 0.21/0.43    r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_relat_1(k6_relat_1(sK1)) | ~v1_funct_1(k6_relat_1(sK1))),
% 0.21/0.43    inference(global_subsumption,[],[f17,f16,f55])).
% 0.21/0.43  fof(f55,plain,(
% 0.21/0.43    ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1)) | r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.21/0.43    inference(duplicate_literal_removal,[],[f54])).
% 0.21/0.43  fof(f54,plain,(
% 0.21/0.43    ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1)) | r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1))),
% 0.21/0.43    inference(resolution,[],[f51,f25])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f51,plain,(
% 0.21/0.43    r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1)))) | ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1))),
% 0.21/0.43    inference(resolution,[],[f49,f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    r2_hidden(sK0,k1_relat_1(sK2)) | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,k6_relat_1(sK1))))),
% 0.21/0.43    inference(cnf_transformation,[],[f13])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (30816)------------------------------
% 0.21/0.43  % (30816)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (30816)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (30816)Memory used [KB]: 6140
% 0.21/0.43  % (30816)Time elapsed: 0.005 s
% 0.21/0.43  % (30816)------------------------------
% 0.21/0.43  % (30816)------------------------------
% 0.21/0.44  % (30811)Success in time 0.077 s
%------------------------------------------------------------------------------
