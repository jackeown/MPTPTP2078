%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1052+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:04 EST 2020

% Result     : Theorem 1.17s
% Output     : Refutation 1.17s
% Verified   : 
% Statistics : Number of formulae       :   40 (  73 expanded)
%              Number of leaves         :   10 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :  224 ( 543 expanded)
%              Number of equality atoms :   71 ( 181 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (12336)dis+1010_2:3_afr=on:afp=40000:afq=1.4:amm=off:anc=none:lma=on:nm=16:nwc=1:sp=occurrence:updr=off:uhcvi=on_34 on theBenchmark
% (12338)dis+4_2_av=off:bs=on:fsr=off:gsp=input_only:newcnf=on:nwc=1:sd=3:ss=axioms:st=3.0:sos=all:sp=reverse_arity:urr=ec_only:updr=off_127 on theBenchmark
fof(f2249,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1838,f1842,f2139,f2228,f2248])).

fof(f2248,plain,
    ( spl16_1
    | ~ spl16_3
    | ~ spl16_22 ),
    inference(avatar_contradiction_clause,[],[f2247])).

fof(f2247,plain,
    ( $false
    | spl16_1
    | ~ spl16_3
    | ~ spl16_22 ),
    inference(subsumption_resolution,[],[f2246,f1834])).

fof(f1834,plain,
    ( sK0 != k1_relat_1(sK2)
    | spl16_1 ),
    inference(avatar_component_clause,[],[f1833])).

fof(f1833,plain,
    ( spl16_1
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_1])])).

fof(f2246,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl16_3
    | ~ spl16_22 ),
    inference(forward_demodulation,[],[f2243,f2138])).

fof(f2138,plain,
    ( sK2 = sK14(sK0,sK1,sK2)
    | ~ spl16_22 ),
    inference(avatar_component_clause,[],[f2137])).

fof(f2137,plain,
    ( spl16_22
  <=> sK2 = sK14(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_22])])).

fof(f2243,plain,
    ( sK0 = k1_relat_1(sK14(sK0,sK1,sK2))
    | ~ spl16_3 ),
    inference(resolution,[],[f1826,f1841])).

fof(f1841,plain,
    ( r2_hidden(sK2,k1_funct_2(sK0,sK1))
    | ~ spl16_3 ),
    inference(avatar_component_clause,[],[f1840])).

fof(f1840,plain,
    ( spl16_3
  <=> r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_3])])).

fof(f1826,plain,(
    ! [X6,X0,X1] :
      ( ~ r2_hidden(X6,k1_funct_2(X0,X1))
      | k1_relat_1(sK14(X0,X1,X6)) = X0 ) ),
    inference(equality_resolution,[],[f1793])).

fof(f1793,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_relat_1(sK14(X0,X1,X6)) = X0
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1721])).

fof(f1721,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X1)
                | k1_relat_1(X4) != X0
                | sK12(X0,X1,X2) != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(sK12(X0,X1,X2),X2) )
          & ( ( r1_tarski(k2_relat_1(sK13(X0,X1,X2)),X1)
              & k1_relat_1(sK13(X0,X1,X2)) = X0
              & sK12(X0,X1,X2) = sK13(X0,X1,X2)
              & v1_funct_1(sK13(X0,X1,X2))
              & v1_relat_1(sK13(X0,X1,X2)) )
            | r2_hidden(sK12(X0,X1,X2),X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X1)
                  | k1_relat_1(X7) != X0
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ( r1_tarski(k2_relat_1(sK14(X0,X1,X6)),X1)
                & k1_relat_1(sK14(X0,X1,X6)) = X0
                & sK14(X0,X1,X6) = X6
                & v1_funct_1(sK14(X0,X1,X6))
                & v1_relat_1(sK14(X0,X1,X6)) )
              | ~ r2_hidden(X6,X2) ) )
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13,sK14])],[f1717,f1720,f1719,f1718])).

fof(f1718,plain,(
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
              | sK12(X0,X1,X2) != X4
              | ~ v1_funct_1(X4)
              | ~ v1_relat_1(X4) )
          | ~ r2_hidden(sK12(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r1_tarski(k2_relat_1(X5),X1)
              & k1_relat_1(X5) = X0
              & sK12(X0,X1,X2) = X5
              & v1_funct_1(X5)
              & v1_relat_1(X5) )
          | r2_hidden(sK12(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1719,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r1_tarski(k2_relat_1(X5),X1)
          & k1_relat_1(X5) = X0
          & sK12(X0,X1,X2) = X5
          & v1_funct_1(X5)
          & v1_relat_1(X5) )
     => ( r1_tarski(k2_relat_1(sK13(X0,X1,X2)),X1)
        & k1_relat_1(sK13(X0,X1,X2)) = X0
        & sK12(X0,X1,X2) = sK13(X0,X1,X2)
        & v1_funct_1(sK13(X0,X1,X2))
        & v1_relat_1(sK13(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1720,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r1_tarski(k2_relat_1(X8),X1)
          & k1_relat_1(X8) = X0
          & X6 = X8
          & v1_funct_1(X8)
          & v1_relat_1(X8) )
     => ( r1_tarski(k2_relat_1(sK14(X0,X1,X6)),X1)
        & k1_relat_1(sK14(X0,X1,X6)) = X0
        & sK14(X0,X1,X6) = X6
        & v1_funct_1(sK14(X0,X1,X6))
        & v1_relat_1(sK14(X0,X1,X6)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1717,plain,(
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
    inference(rectify,[],[f1716])).

fof(f1716,plain,(
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
    inference(nnf_transformation,[],[f1477])).

fof(f1477,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_funct_2)).

fof(f2228,plain,
    ( spl16_2
    | ~ spl16_3
    | ~ spl16_22 ),
    inference(avatar_split_clause,[],[f2226,f2137,f1840,f1836])).

fof(f1836,plain,
    ( spl16_2
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_2])])).

fof(f2226,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl16_3
    | ~ spl16_22 ),
    inference(forward_demodulation,[],[f2223,f2138])).

fof(f2223,plain,
    ( r1_tarski(k2_relat_1(sK14(sK0,sK1,sK2)),sK1)
    | ~ spl16_3 ),
    inference(resolution,[],[f1825,f1841])).

fof(f1825,plain,(
    ! [X6,X0,X1] :
      ( ~ r2_hidden(X6,k1_funct_2(X0,X1))
      | r1_tarski(k2_relat_1(sK14(X0,X1,X6)),X1) ) ),
    inference(equality_resolution,[],[f1794])).

fof(f1794,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_tarski(k2_relat_1(sK14(X0,X1,X6)),X1)
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1721])).

fof(f2139,plain,
    ( spl16_22
    | ~ spl16_3 ),
    inference(avatar_split_clause,[],[f2133,f1840,f2137])).

fof(f2133,plain,
    ( sK2 = sK14(sK0,sK1,sK2)
    | ~ spl16_3 ),
    inference(resolution,[],[f1827,f1841])).

fof(f1827,plain,(
    ! [X6,X0,X1] :
      ( ~ r2_hidden(X6,k1_funct_2(X0,X1))
      | sK14(X0,X1,X6) = X6 ) ),
    inference(equality_resolution,[],[f1792])).

fof(f1792,plain,(
    ! [X6,X2,X0,X1] :
      ( sK14(X0,X1,X6) = X6
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1721])).

fof(f1842,plain,(
    spl16_3 ),
    inference(avatar_split_clause,[],[f1726,f1840])).

fof(f1726,plain,(
    r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f1692])).

fof(f1692,plain,
    ( ( ~ r1_tarski(k2_relat_1(sK2),sK1)
      | sK0 != k1_relat_1(sK2) )
    & r2_hidden(sK2,k1_funct_2(sK0,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f1634,f1691])).

fof(f1691,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_tarski(k2_relat_1(X2),X1)
          | k1_relat_1(X2) != X0 )
        & r2_hidden(X2,k1_funct_2(X0,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ( ~ r1_tarski(k2_relat_1(sK2),sK1)
        | sK0 != k1_relat_1(sK2) )
      & r2_hidden(sK2,k1_funct_2(sK0,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f1634,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k2_relat_1(X2),X1)
        | k1_relat_1(X2) != X0 )
      & r2_hidden(X2,k1_funct_2(X0,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f1633])).

fof(f1633,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k2_relat_1(X2),X1)
        | k1_relat_1(X2) != X0 )
      & r2_hidden(X2,k1_funct_2(X0,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1566])).

fof(f1566,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X2,k1_funct_2(X0,X1))
         => ( r1_tarski(k2_relat_1(X2),X1)
            & k1_relat_1(X2) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f1565])).

fof(f1565,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( r1_tarski(k2_relat_1(X2),X1)
          & k1_relat_1(X2) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_funct_2)).

fof(f1838,plain,
    ( ~ spl16_1
    | ~ spl16_2 ),
    inference(avatar_split_clause,[],[f1727,f1836,f1833])).

fof(f1727,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | sK0 != k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f1692])).
%------------------------------------------------------------------------------
