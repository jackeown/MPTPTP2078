%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0748+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   32 ( 125 expanded)
%              Number of leaves         :    6 (  36 expanded)
%              Depth                    :   13
%              Number of atoms          :   96 ( 527 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f60,plain,(
    $false ),
    inference(resolution,[],[f59,f40])).

fof(f40,plain,(
    ! [X3] : r2_hidden(sK1(sK2(X3)),sK0) ),
    inference(subsumption_resolution,[],[f37,f16])).

% (8716)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
fof(f16,plain,(
    ! [X1] :
      ( ~ v3_ordinal1(X1)
      | r2_hidden(X1,sK0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK0)
      | ~ v3_ordinal1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f5,f7])).

fof(f7,plain,
    ( ? [X0] :
      ! [X1] :
        ( r2_hidden(X1,X0)
        | ~ v3_ordinal1(X1) )
   => ! [X1] :
        ( r2_hidden(X1,sK0)
        | ~ v3_ordinal1(X1) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0] :
    ! [X1] :
      ( r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ~ ! [X1] :
            ( v3_ordinal1(X1)
           => r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ~ ! [X1] :
          ( v3_ordinal1(X1)
         => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_ordinal1)).

fof(f37,plain,(
    ! [X3] :
      ( r2_hidden(sK1(sK2(X3)),sK0)
      | v3_ordinal1(sK1(sK2(X3))) ) ),
    inference(resolution,[],[f22,f20])).

fof(f20,plain,(
    ! [X2,X0] :
      ( v3_ordinal1(X2)
      | ~ r2_hidden(X2,sK2(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X2] :
      ( ( r2_hidden(X2,sK2(X0))
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,X0) )
      & ( ( v3_ordinal1(X2)
          & r2_hidden(X2,X0) )
        | ~ r2_hidden(X2,sK2(X0)) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f14])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] :
        ! [X2] :
          ( ( r2_hidden(X2,X1)
            | ~ v3_ordinal1(X2)
            | ~ r2_hidden(X2,X0) )
          & ( ( v3_ordinal1(X2)
              & r2_hidden(X2,X0) )
            | ~ r2_hidden(X2,X1) ) )
     => ! [X2] :
          ( ( r2_hidden(X2,sK2(X0))
            | ~ v3_ordinal1(X2)
            | ~ r2_hidden(X2,X0) )
          & ( ( v3_ordinal1(X2)
              & r2_hidden(X2,X0) )
            | ~ r2_hidden(X2,sK2(X0)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( ( r2_hidden(X2,X1)
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,X0) )
      & ( ( v3_ordinal1(X2)
          & r2_hidden(X2,X0) )
        | ~ r2_hidden(X2,X1) ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( ( r2_hidden(X2,X1)
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,X0) )
      & ( ( v3_ordinal1(X2)
          & r2_hidden(X2,X0) )
        | ~ r2_hidden(X2,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( r2_hidden(X2,X1)
    <=> ( v3_ordinal1(X2)
        & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s1_xboole_0__e3_53__ordinal1)).

fof(f22,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),sK0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(resolution,[],[f16,f17])).

fof(f17,plain,(
    ! [X0] :
      ( v3_ordinal1(sK1(X0))
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( ~ v3_ordinal1(sK1(X0))
        | ~ r2_hidden(sK1(X0),X0) )
      & ( v3_ordinal1(sK1(X0))
        | r2_hidden(sK1(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f9,f10])).

fof(f10,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v3_ordinal1(X1)
            | ~ r2_hidden(X1,X0) )
          & ( v3_ordinal1(X1)
            | r2_hidden(X1,X0) ) )
     => ( ( ~ v3_ordinal1(sK1(X0))
          | ~ r2_hidden(sK1(X0),X0) )
        & ( v3_ordinal1(sK1(X0))
          | r2_hidden(sK1(X0),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X0] :
    ? [X1] :
      ( ( ~ v3_ordinal1(X1)
        | ~ r2_hidden(X1,X0) )
      & ( v3_ordinal1(X1)
        | r2_hidden(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0] :
    ? [X1] :
      ( r2_hidden(X1,X0)
    <~> v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ! [X1] :
          ( r2_hidden(X1,X0)
        <=> v3_ordinal1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_ordinal1)).

fof(f59,plain,(
    ! [X2] : ~ r2_hidden(sK1(sK2(X2)),X2) ),
    inference(subsumption_resolution,[],[f57,f51])).

fof(f51,plain,(
    ! [X1] : v3_ordinal1(sK1(sK2(X1))) ),
    inference(subsumption_resolution,[],[f48,f20])).

fof(f48,plain,(
    ! [X1] :
      ( r2_hidden(sK1(sK2(X1)),sK2(sK0))
      | v3_ordinal1(sK1(sK2(X1))) ) ),
    inference(resolution,[],[f27,f17])).

fof(f27,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,sK2(X2))
      | r2_hidden(X1,sK2(sK0)) ) ),
    inference(subsumption_resolution,[],[f25,f20])).

fof(f25,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,sK2(X2))
      | r2_hidden(X1,sK2(sK0))
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f23,f21])).

fof(f21,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,sK2(X0))
      | ~ v3_ordinal1(X2)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f23,plain,(
    ! [X2,X1] :
      ( r2_hidden(X1,sK0)
      | ~ r2_hidden(X1,sK2(X2)) ) ),
    inference(resolution,[],[f16,f20])).

fof(f57,plain,(
    ! [X2] :
      ( ~ v3_ordinal1(sK1(sK2(X2)))
      | ~ r2_hidden(sK1(sK2(X2)),X2) ) ),
    inference(resolution,[],[f52,f21])).

fof(f52,plain,(
    ! [X0] : ~ r2_hidden(sK1(sK2(X0)),sK2(X0)) ),
    inference(resolution,[],[f51,f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(sK1(X0))
      | ~ r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f11])).

%------------------------------------------------------------------------------
