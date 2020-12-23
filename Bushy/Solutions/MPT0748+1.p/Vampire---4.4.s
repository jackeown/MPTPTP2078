%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : ordinal1__t38_ordinal1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:26 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   27 (  65 expanded)
%              Number of leaves         :    6 (  18 expanded)
%              Depth                    :   10
%              Number of atoms          :   86 ( 259 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f202,plain,(
    $false ),
    inference(resolution,[],[f200,f89])).

fof(f89,plain,(
    ! [X0] : ~ r2_hidden(sK1(sK3(X0)),sK3(X0)) ),
    inference(resolution,[],[f41,f72])).

fof(f72,plain,(
    ! [X0] : v3_ordinal1(sK1(sK3(X0))) ),
    inference(duplicate_literal_removal,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( v3_ordinal1(sK1(sK3(X0)))
      | v3_ordinal1(sK1(sK3(X0))) ) ),
    inference(resolution,[],[f40,f44])).

fof(f44,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,sK3(X0))
      | v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X2] :
      ( ( r2_hidden(X2,sK3(X0))
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,X0) )
      & ( ( v3_ordinal1(X2)
          & r2_hidden(X2,X0) )
        | ~ r2_hidden(X2,sK3(X0)) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f34])).

fof(f34,plain,(
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
          ( ( r2_hidden(X2,sK3(X0))
            | ~ v3_ordinal1(X2)
            | ~ r2_hidden(X2,X0) )
          & ( ( v3_ordinal1(X2)
              & r2_hidden(X2,X0) )
            | ~ r2_hidden(X2,sK3(X0)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( ( r2_hidden(X2,X1)
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,X0) )
      & ( ( v3_ordinal1(X2)
          & r2_hidden(X2,X0) )
        | ~ r2_hidden(X2,X1) ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( ( r2_hidden(X2,X1)
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,X0) )
      & ( ( v3_ordinal1(X2)
          & r2_hidden(X2,X0) )
        | ~ r2_hidden(X2,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( r2_hidden(X2,X1)
    <=> ( v3_ordinal1(X2)
        & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t38_ordinal1.p',s1_xboole_0__e3_53__ordinal1)).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v3_ordinal1(sK1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( ~ v3_ordinal1(sK1(X0))
        | ~ r2_hidden(sK1(X0),X0) )
      & ( v3_ordinal1(sK1(X0))
        | r2_hidden(sK1(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).

fof(f28,plain,(
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

fof(f27,plain,(
    ! [X0] :
    ? [X1] :
      ( ( ~ v3_ordinal1(X1)
        | ~ r2_hidden(X1,X0) )
      & ( v3_ordinal1(X1)
        | r2_hidden(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
    ? [X1] :
      ( r2_hidden(X1,X0)
    <~> v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ~ ! [X1] :
          ( r2_hidden(X1,X0)
        <=> v3_ordinal1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t38_ordinal1.p',t37_ordinal1)).

fof(f41,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(sK1(X0))
      | ~ r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f200,plain,(
    ! [X1] : r2_hidden(sK1(sK3(X1)),sK3(sK0)) ),
    inference(subsumption_resolution,[],[f198,f72])).

fof(f198,plain,(
    ! [X1] :
      ( r2_hidden(sK1(sK3(X1)),sK3(sK0))
      | ~ v3_ordinal1(sK1(sK3(X1))) ) ),
    inference(resolution,[],[f96,f36])).

fof(f36,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK0)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK0)
      | ~ v3_ordinal1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f25])).

fof(f25,plain,
    ( ? [X0] :
      ! [X1] :
        ( r2_hidden(X1,X0)
        | ~ v3_ordinal1(X1) )
   => ! [X1] :
        ( r2_hidden(X1,sK0)
        | ~ v3_ordinal1(X1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
    ! [X1] :
      ( r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ~ ! [X1] :
            ( v3_ordinal1(X1)
           => r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ~ ! [X1] :
          ( v3_ordinal1(X1)
         => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t38_ordinal1.p',t38_ordinal1)).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK1(sK3(X0)),X1)
      | r2_hidden(sK1(sK3(X0)),sK3(X1)) ) ),
    inference(resolution,[],[f45,f72])).

fof(f45,plain,(
    ! [X2,X0] :
      ( ~ v3_ordinal1(X2)
      | r2_hidden(X2,sK3(X0))
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
