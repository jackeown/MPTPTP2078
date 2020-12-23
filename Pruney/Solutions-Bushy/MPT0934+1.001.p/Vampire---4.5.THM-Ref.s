%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0934+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:56 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   34 (  92 expanded)
%              Number of leaves         :    7 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :  147 ( 573 expanded)
%              Number of equality atoms :   49 ( 253 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f54,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f15,f16,f17,f18,f38,f27,f26,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | sQ3_eqProxy(X1,X0)
      | ~ sQ3_eqProxy(k2_mcart_1(X0),k2_mcart_1(X1))
      | ~ sQ3_eqProxy(k1_mcart_1(X0),k1_mcart_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,X2)
      | ~ m1_subset_1(X0,X2) ) ),
    inference(duplicate_literal_removal,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ sQ3_eqProxy(k1_mcart_1(X0),k1_mcart_1(X1))
      | sQ3_eqProxy(X1,X0)
      | ~ sQ3_eqProxy(k2_mcart_1(X0),k2_mcart_1(X1))
      | ~ v1_relat_1(X2)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,X2)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X0,X2) ) ),
    inference(resolution,[],[f40,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ sQ3_eqProxy(k1_mcart_1(X0),k1_mcart_1(X1))
      | sQ3_eqProxy(X1,X0)
      | ~ sQ3_eqProxy(k2_mcart_1(X0),k2_mcart_1(X1))
      | ~ v1_relat_1(X2)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,X2) ) ),
    inference(resolution,[],[f28,f23])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sQ3_eqProxy(k2_mcart_1(X2),k2_mcart_1(X0))
      | ~ sQ3_eqProxy(k1_mcart_1(X2),k1_mcart_1(X0))
      | sQ3_eqProxy(X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_proxy_replacement,[],[f22,f24,f24,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( sQ3_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | k2_mcart_1(X2) != k2_mcart_1(X0)
      | k1_mcart_1(X2) != k1_mcart_1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X0 = X2
          | k2_mcart_1(X2) != k2_mcart_1(X0)
          | k1_mcart_1(X2) != k1_mcart_1(X0)
          | ~ r2_hidden(X0,X1)
          | ~ r2_hidden(X2,X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X0 = X2
          | k2_mcart_1(X2) != k2_mcart_1(X0)
          | k1_mcart_1(X2) != k1_mcart_1(X0)
          | ~ r2_hidden(X0,X1)
          | ~ r2_hidden(X2,X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( ( k2_mcart_1(X2) = k2_mcart_1(X0)
            & k1_mcart_1(X2) = k1_mcart_1(X0)
            & r2_hidden(X0,X1)
            & r2_hidden(X2,X1) )
         => X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_mcart_1)).

fof(f26,plain,(
    sQ3_eqProxy(k2_mcart_1(sK1),k2_mcart_1(sK2)) ),
    inference(equality_proxy_replacement,[],[f20,f24])).

fof(f20,plain,(
    k2_mcart_1(sK1) = k2_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( sK1 != sK2
    & k2_mcart_1(sK1) = k2_mcart_1(sK2)
    & k1_mcart_1(sK1) = k1_mcart_1(sK2)
    & m1_subset_1(sK2,sK0)
    & m1_subset_1(sK1,sK0)
    & v1_relat_1(sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f13,f12,f11])).

fof(f11,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( X1 != X2
                & k2_mcart_1(X2) = k2_mcart_1(X1)
                & k1_mcart_1(X2) = k1_mcart_1(X1)
                & m1_subset_1(X2,X0) )
            & m1_subset_1(X1,X0) )
        & v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k2_mcart_1(X2) = k2_mcart_1(X1)
              & k1_mcart_1(X2) = k1_mcart_1(X1)
              & m1_subset_1(X2,sK0) )
          & m1_subset_1(X1,sK0) )
      & v1_relat_1(sK0)
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( X1 != X2
            & k2_mcart_1(X2) = k2_mcart_1(X1)
            & k1_mcart_1(X2) = k1_mcart_1(X1)
            & m1_subset_1(X2,sK0) )
        & m1_subset_1(X1,sK0) )
   => ( ? [X2] :
          ( sK1 != X2
          & k2_mcart_1(X2) = k2_mcart_1(sK1)
          & k1_mcart_1(X2) = k1_mcart_1(sK1)
          & m1_subset_1(X2,sK0) )
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X2] :
        ( sK1 != X2
        & k2_mcart_1(X2) = k2_mcart_1(sK1)
        & k1_mcart_1(X2) = k1_mcart_1(sK1)
        & m1_subset_1(X2,sK0) )
   => ( sK1 != sK2
      & k2_mcart_1(sK1) = k2_mcart_1(sK2)
      & k1_mcart_1(sK1) = k1_mcart_1(sK2)
      & m1_subset_1(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k2_mcart_1(X2) = k2_mcart_1(X1)
              & k1_mcart_1(X2) = k1_mcart_1(X1)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,X0) )
      & v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k2_mcart_1(X2) = k2_mcart_1(X1)
              & k1_mcart_1(X2) = k1_mcart_1(X1)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,X0) )
      & v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_relat_1(X0)
          & ~ v1_xboole_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,X0)
               => ( ( k2_mcart_1(X2) = k2_mcart_1(X1)
                    & k1_mcart_1(X2) = k1_mcart_1(X1) )
                 => X1 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ( ( k2_mcart_1(X2) = k2_mcart_1(X1)
                  & k1_mcart_1(X2) = k1_mcart_1(X1) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_mcart_1)).

fof(f27,plain,(
    sQ3_eqProxy(k1_mcart_1(sK1),k1_mcart_1(sK2)) ),
    inference(equality_proxy_replacement,[],[f19,f24])).

fof(f19,plain,(
    k1_mcart_1(sK1) = k1_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f38,plain,(
    ~ sQ3_eqProxy(sK2,sK1) ),
    inference(resolution,[],[f36,f25])).

fof(f25,plain,(
    ~ sQ3_eqProxy(sK1,sK2) ),
    inference(equality_proxy_replacement,[],[f21,f24])).

fof(f21,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0,X1] :
      ( sQ3_eqProxy(X1,X0)
      | ~ sQ3_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f24])).

fof(f18,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f17,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f16,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

%------------------------------------------------------------------------------
