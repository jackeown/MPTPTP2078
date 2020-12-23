%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0541+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   30 (  80 expanded)
%              Number of leaves         :    3 (  16 expanded)
%              Depth                    :   13
%              Number of atoms          :   94 ( 301 expanded)
%              Number of equality atoms :    7 (  19 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f71,plain,(
    $false ),
    inference(subsumption_resolution,[],[f70,f60])).

fof(f60,plain,(
    ~ r2_hidden(sK0,k9_relat_1(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f59,f11])).

fof(f11,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <~> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X0,k9_relat_1(X2,X1))
        <=> ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f59,plain,
    ( ~ r2_hidden(sK0,k9_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2) ),
    inference(duplicate_literal_removal,[],[f58])).

fof(f58,plain,
    ( ~ r2_hidden(sK0,k9_relat_1(sK2,sK1))
    | ~ r2_hidden(sK0,k9_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | ~ r2_hidden(sK0,k9_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f55,f23])).

fof(f23,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK5(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK5(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).

fof(f55,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(sK2,X0,sK0),sK1)
      | ~ r2_hidden(sK0,k9_relat_1(sK2,sK1))
      | ~ r2_hidden(sK0,k9_relat_1(sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f54,f11])).

fof(f54,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(sK2,X0,sK0),sK1)
      | ~ r2_hidden(sK0,k9_relat_1(sK2,sK1))
      | ~ v1_relat_1(sK2)
      | ~ r2_hidden(sK0,k9_relat_1(sK2,X0)) ) ),
    inference(resolution,[],[f27,f24])).

fof(f24,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK5(X0,X1,X3),X3),X0)
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f15])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK5(X0,X1,X3),X3),X0)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X3] :
      ( ~ r2_hidden(k4_tarski(X3,sK0),sK2)
      | ~ r2_hidden(X3,sK1)
      | ~ r2_hidden(sK0,k9_relat_1(sK2,sK1)) ) ),
    inference(subsumption_resolution,[],[f7,f26])).

fof(f26,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f7,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_relat_1(sK2))
      | ~ r2_hidden(k4_tarski(X3,sK0),sK2)
      | ~ r2_hidden(X3,sK1)
      | ~ r2_hidden(sK0,k9_relat_1(sK2,sK1)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f70,plain,(
    r2_hidden(sK0,k9_relat_1(sK2,sK1)) ),
    inference(duplicate_literal_removal,[],[f67])).

fof(f67,plain,
    ( r2_hidden(sK0,k9_relat_1(sK2,sK1))
    | r2_hidden(sK0,k9_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f62,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,X0)
      | r2_hidden(sK0,k9_relat_1(sK2,sK1))
      | r2_hidden(sK0,k9_relat_1(sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f49,f11])).

fof(f49,plain,(
    ! [X0] :
      ( r2_hidden(sK0,k9_relat_1(sK2,sK1))
      | ~ v1_relat_1(sK2)
      | ~ r2_hidden(sK3,X0)
      | r2_hidden(sK0,k9_relat_1(sK2,X0)) ) ),
    inference(resolution,[],[f9,f22])).

fof(f22,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f9,plain,
    ( r2_hidden(k4_tarski(sK3,sK0),sK2)
    | r2_hidden(sK0,k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f62,plain,(
    r2_hidden(sK3,sK1) ),
    inference(resolution,[],[f60,f10])).

fof(f10,plain,
    ( r2_hidden(sK0,k9_relat_1(sK2,sK1))
    | r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f5])).

%------------------------------------------------------------------------------
