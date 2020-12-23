%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 659 expanded)
%              Number of leaves         :    7 ( 197 expanded)
%              Depth                    :   26
%              Number of atoms          :  273 (4843 expanded)
%              Number of equality atoms :   62 (1658 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f111,plain,(
    $false ),
    inference(subsumption_resolution,[],[f110,f22])).

fof(f22,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( sK0 != sK1
    & ! [X2] :
        ( k1_funct_1(sK0,X2) = k1_funct_1(sK1,X2)
        | ~ r2_hidden(X2,k1_relat_1(sK0)) )
    & k1_relat_1(sK0) = k1_relat_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f14,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & ! [X2] :
                ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                | ~ r2_hidden(X2,k1_relat_1(X0)) )
            & k1_relat_1(X0) = k1_relat_1(X1)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( sK0 != X1
          & ! [X2] :
              ( k1_funct_1(X1,X2) = k1_funct_1(sK0,X2)
              | ~ r2_hidden(X2,k1_relat_1(sK0)) )
          & k1_relat_1(X1) = k1_relat_1(sK0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X1] :
        ( sK0 != X1
        & ! [X2] :
            ( k1_funct_1(X1,X2) = k1_funct_1(sK0,X2)
            | ~ r2_hidden(X2,k1_relat_1(sK0)) )
        & k1_relat_1(X1) = k1_relat_1(sK0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( sK0 != sK1
      & ! [X2] :
          ( k1_funct_1(sK0,X2) = k1_funct_1(sK1,X2)
          | ~ r2_hidden(X2,k1_relat_1(sK0)) )
      & k1_relat_1(sK0) = k1_relat_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & ! [X2] :
              ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          & k1_relat_1(X0) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & ! [X2] :
              ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          & k1_relat_1(X0) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( ! [X2] :
                    ( r2_hidden(X2,k1_relat_1(X0))
                   => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
                & k1_relat_1(X0) = k1_relat_1(X1) )
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

fof(f110,plain,(
    ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f109,f24])).

fof(f24,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f109,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f108,f99])).

fof(f99,plain,(
    r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0) ),
    inference(backward_demodulation,[],[f79,f96])).

fof(f96,plain,(
    sK3(sK0,sK1) = k1_funct_1(sK0,sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f95,f22])).

fof(f95,plain,
    ( sK3(sK0,sK1) = k1_funct_1(sK0,sK2(sK0,sK1))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f94,f23])).

fof(f23,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f94,plain,
    ( sK3(sK0,sK1) = k1_funct_1(sK0,sK2(sK0,sK1))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(duplicate_literal_removal,[],[f91])).

fof(f91,plain,
    ( sK3(sK0,sK1) = k1_funct_1(sK0,sK2(sK0,sK1))
    | sK3(sK0,sK1) = k1_funct_1(sK0,sK2(sK0,sK1))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f77,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f77,plain,
    ( r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0)
    | sK3(sK0,sK1) = k1_funct_1(sK0,sK2(sK0,sK1)) ),
    inference(backward_demodulation,[],[f54,f74])).

fof(f74,plain,(
    k1_funct_1(sK1,sK2(sK0,sK1)) = k1_funct_1(sK0,sK2(sK0,sK1)) ),
    inference(resolution,[],[f72,f27])).

fof(f27,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_relat_1(sK0))
      | k1_funct_1(sK0,X2) = k1_funct_1(sK1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f72,plain,(
    r2_hidden(sK2(sK0,sK1),k1_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f68,f22])).

fof(f68,plain,
    ( r2_hidden(sK2(sK0,sK1),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(duplicate_literal_removal,[],[f67])).

fof(f67,plain,
    ( r2_hidden(sK2(sK0,sK1),k1_relat_1(sK0))
    | r2_hidden(sK2(sK0,sK1),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f57,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

fof(f57,plain,
    ( r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0)
    | r2_hidden(sK2(sK0,sK1),k1_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f56,f26])).

fof(f26,plain,(
    k1_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f56,plain,
    ( r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0)
    | r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f52,f24])).

fof(f52,plain,
    ( r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0)
    | r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f49,f33])).

fof(f49,plain,
    ( r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK1)
    | r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0) ),
    inference(subsumption_resolution,[],[f47,f28])).

fof(f28,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f15])).

fof(f47,plain,
    ( r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0)
    | r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK1)
    | sK0 = sK1 ),
    inference(resolution,[],[f44,f24])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK2(sK0,X0),sK3(sK0,X0)),sK0)
      | r2_hidden(k4_tarski(sK2(sK0,X0),sK3(sK0,X0)),X0)
      | sK0 = X0 ) ),
    inference(resolution,[],[f31,f22])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | ~ v1_relat_1(X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ( ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
                  | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) )
                & ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
                  | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) )
                  & ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f17,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
            | ~ r2_hidden(k4_tarski(X2,X3),X0) )
          & ( r2_hidden(k4_tarski(X2,X3),X1)
            | r2_hidden(k4_tarski(X2,X3),X0) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
          | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) )
        & ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
          | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | r2_hidden(k4_tarski(X2,X3),X0) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) )
                  & ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | r2_hidden(k4_tarski(X2,X3),X0) ) ) )
            & ( ! [X2,X3] :
                  ( ( r2_hidden(k4_tarski(X2,X3),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( X0 = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X0)
              <=> r2_hidden(k4_tarski(X2,X3),X1) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( X0 = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X0)
              <=> r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_relat_1)).

fof(f54,plain,
    ( r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0)
    | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f53,f24])).

fof(f53,plain,
    ( r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0)
    | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f50,f25])).

fof(f25,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f50,plain,
    ( r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0)
    | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f49,f36])).

fof(f79,plain,(
    r2_hidden(k4_tarski(sK2(sK0,sK1),k1_funct_1(sK0,sK2(sK0,sK1))),sK0) ),
    inference(subsumption_resolution,[],[f78,f22])).

fof(f78,plain,
    ( r2_hidden(k4_tarski(sK2(sK0,sK1),k1_funct_1(sK0,sK2(sK0,sK1))),sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f75,f23])).

fof(f75,plain,
    ( r2_hidden(k4_tarski(sK2(sK0,sK1),k1_funct_1(sK0,sK2(sK0,sK1))),sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f72,f40])).

% (6945)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
fof(f40,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f108,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f105,f28])).

fof(f105,plain,
    ( sK0 = sK1
    | ~ r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f98,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
      | X0 = X1
      | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f98,plain,(
    r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK1) ),
    inference(backward_demodulation,[],[f76,f96])).

fof(f76,plain,(
    r2_hidden(k4_tarski(sK2(sK0,sK1),k1_funct_1(sK0,sK2(sK0,sK1))),sK1) ),
    inference(backward_demodulation,[],[f73,f74])).

fof(f73,plain,(
    r2_hidden(k4_tarski(sK2(sK0,sK1),k1_funct_1(sK1,sK2(sK0,sK1))),sK1) ),
    inference(resolution,[],[f72,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK0))
      | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1) ) ),
    inference(subsumption_resolution,[],[f42,f24])).

fof(f42,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK0))
      | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f41,f25])).

fof(f41,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK0))
      | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f40,f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:48:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (6956)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.51  % (6958)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (6946)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (6942)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (6942)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f110,f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    v1_relat_1(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    (sK0 != sK1 & ! [X2] : (k1_funct_1(sK0,X2) = k1_funct_1(sK1,X2) | ~r2_hidden(X2,k1_relat_1(sK0))) & k1_relat_1(sK0) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f14,f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (X0 != X1 & ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) & k1_relat_1(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (sK0 != X1 & ! [X2] : (k1_funct_1(X1,X2) = k1_funct_1(sK0,X2) | ~r2_hidden(X2,k1_relat_1(sK0))) & k1_relat_1(X1) = k1_relat_1(sK0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ? [X1] : (sK0 != X1 & ! [X2] : (k1_funct_1(X1,X2) = k1_funct_1(sK0,X2) | ~r2_hidden(X2,k1_relat_1(sK0))) & k1_relat_1(X1) = k1_relat_1(sK0) & v1_funct_1(X1) & v1_relat_1(X1)) => (sK0 != sK1 & ! [X2] : (k1_funct_1(sK0,X2) = k1_funct_1(sK1,X2) | ~r2_hidden(X2,k1_relat_1(sK0))) & k1_relat_1(sK0) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f7,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (X0 != X1 & ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) & k1_relat_1(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.52    inference(flattening,[],[f6])).
% 0.21/0.52  fof(f6,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((X0 != X1 & (! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) & k1_relat_1(X0) = k1_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,negated_conjecture,(
% 0.21/0.52    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 0.21/0.52    inference(negated_conjecture,[],[f4])).
% 0.21/0.52  fof(f4,conjecture,(
% 0.21/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    ~v1_relat_1(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f109,f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    v1_relat_1(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f108,f99])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0)),
% 0.21/0.52    inference(backward_demodulation,[],[f79,f96])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    sK3(sK0,sK1) = k1_funct_1(sK0,sK2(sK0,sK1))),
% 0.21/0.52    inference(subsumption_resolution,[],[f95,f22])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    sK3(sK0,sK1) = k1_funct_1(sK0,sK2(sK0,sK1)) | ~v1_relat_1(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f94,f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    v1_funct_1(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    sK3(sK0,sK1) = k1_funct_1(sK0,sK2(sK0,sK1)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f91])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    sK3(sK0,sK1) = k1_funct_1(sK0,sK2(sK0,sK1)) | sK3(sK0,sK1) = k1_funct_1(sK0,sK2(sK0,sK1)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 0.21/0.52    inference(resolution,[],[f77,f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(flattening,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(nnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(flattening,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0) | sK3(sK0,sK1) = k1_funct_1(sK0,sK2(sK0,sK1))),
% 0.21/0.52    inference(backward_demodulation,[],[f54,f74])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    k1_funct_1(sK1,sK2(sK0,sK1)) = k1_funct_1(sK0,sK2(sK0,sK1))),
% 0.21/0.52    inference(resolution,[],[f72,f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X2] : (~r2_hidden(X2,k1_relat_1(sK0)) | k1_funct_1(sK0,X2) = k1_funct_1(sK1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    r2_hidden(sK2(sK0,sK1),k1_relat_1(sK0))),
% 0.21/0.52    inference(subsumption_resolution,[],[f68,f22])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    r2_hidden(sK2(sK0,sK1),k1_relat_1(sK0)) | ~v1_relat_1(sK0)),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f67])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    r2_hidden(sK2(sK0,sK1),k1_relat_1(sK0)) | r2_hidden(sK2(sK0,sK1),k1_relat_1(sK0)) | ~v1_relat_1(sK0)),
% 0.21/0.52    inference(resolution,[],[f57,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(flattening,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0) | r2_hidden(sK2(sK0,sK1),k1_relat_1(sK0))),
% 0.21/0.52    inference(forward_demodulation,[],[f56,f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    k1_relat_1(sK0) = k1_relat_1(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0) | r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1))),
% 0.21/0.52    inference(subsumption_resolution,[],[f52,f24])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0) | r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 0.21/0.52    inference(resolution,[],[f49,f33])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK1) | r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f47,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    sK0 != sK1),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0) | r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK1) | sK0 = sK1),
% 0.21/0.52    inference(resolution,[],[f44,f24])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK2(sK0,X0),sK3(sK0,X0)),sK0) | r2_hidden(k4_tarski(sK2(sK0,X0),sK3(sK0,X0)),X0) | sK0 = X0) )),
% 0.21/0.52    inference(resolution,[],[f31,f22])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | ~v1_relat_1(X1) | X0 = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((X0 = X1 | ((~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(k4_tarski(X4,X5),X1)) & (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0))) | X0 != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f17,f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2,X3] : ((~r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) & (r2_hidden(k4_tarski(X2,X3),X1) | r2_hidden(k4_tarski(X2,X3),X0))) => ((~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((X0 = X1 | ? [X2,X3] : ((~r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) & (r2_hidden(k4_tarski(X2,X3),X1) | r2_hidden(k4_tarski(X2,X3),X0)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(k4_tarski(X4,X5),X1)) & (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0))) | X0 != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(rectify,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((X0 = X1 | ? [X2,X3] : ((~r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) & (r2_hidden(k4_tarski(X2,X3),X1) | r2_hidden(k4_tarski(X2,X3),X0)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | X0 != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((X0 = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) <=> r2_hidden(k4_tarski(X2,X3),X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (X0 = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) <=> r2_hidden(k4_tarski(X2,X3),X1)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_relat_1)).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0) | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))),
% 0.21/0.52    inference(subsumption_resolution,[],[f53,f24])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0) | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) | ~v1_relat_1(sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f50,f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    v1_funct_1(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0) | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.21/0.52    inference(resolution,[],[f49,f36])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK2(sK0,sK1),k1_funct_1(sK0,sK2(sK0,sK1))),sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f78,f22])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK2(sK0,sK1),k1_funct_1(sK0,sK2(sK0,sK1))),sK0) | ~v1_relat_1(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f75,f23])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK2(sK0,sK1),k1_funct_1(sK0,sK2(sK0,sK1))),sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 0.21/0.52    inference(resolution,[],[f72,f40])).
% 0.21/0.52  % (6945)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X2,X0] : (~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(equality_resolution,[],[f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    ~r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f105,f28])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    sK0 = sK1 | ~r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 0.21/0.52    inference(resolution,[],[f98,f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) | X0 = X1 | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK1)),
% 0.21/0.52    inference(backward_demodulation,[],[f76,f96])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK2(sK0,sK1),k1_funct_1(sK0,sK2(sK0,sK1))),sK1)),
% 0.21/0.52    inference(backward_demodulation,[],[f73,f74])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK2(sK0,sK1),k1_funct_1(sK1,sK2(sK0,sK1))),sK1)),
% 0.21/0.52    inference(resolution,[],[f72,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK0)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f42,f24])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK0)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1) | ~v1_relat_1(sK1)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f41,f25])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK0)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 0.21/0.52    inference(superposition,[],[f40,f26])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (6942)------------------------------
% 0.21/0.52  % (6942)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (6942)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (6942)Memory used [KB]: 6140
% 0.21/0.52  % (6942)Time elapsed: 0.101 s
% 0.21/0.52  % (6942)------------------------------
% 0.21/0.52  % (6942)------------------------------
% 0.21/0.52  % (6944)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.52  % (6938)Success in time 0.156 s
%------------------------------------------------------------------------------
