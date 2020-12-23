%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0669+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:43 EST 2020

% Result     : Theorem 1.11s
% Output     : Refutation 1.11s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 176 expanded)
%              Number of leaves         :    9 (  43 expanded)
%              Depth                    :   18
%              Number of atoms          :  351 (1189 expanded)
%              Number of equality atoms :   29 (  81 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5665,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f5440,f5635,f5658,f5664])).

fof(f5664,plain,
    ( ~ spl205_1
    | spl205_2 ),
    inference(avatar_contradiction_clause,[],[f5663])).

fof(f5663,plain,
    ( $false
    | ~ spl205_1
    | spl205_2 ),
    inference(unit_resulting_resolution,[],[f2410,f2411,f5435,f5438,f5589])).

fof(f5589,plain,(
    ! [X6,X2,X0] :
      ( ~ r2_hidden(X6,k1_relat_1(k8_relat_1(X0,X2)))
      | r2_hidden(X6,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f5588,f2892])).

fof(f2892,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1218])).

fof(f1218,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f670])).

fof(f670,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f5588,plain,(
    ! [X6,X2,X0] :
      ( r2_hidden(X6,k1_relat_1(X2))
      | ~ r2_hidden(X6,k1_relat_1(k8_relat_1(X0,X2)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(k8_relat_1(X0,X2)) ) ),
    inference(subsumption_resolution,[],[f4075,f3160])).

fof(f3160,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k8_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1488])).

fof(f1488,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1487])).

fof(f1487,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f909])).

fof(f909,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_funct_1)).

fof(f4075,plain,(
    ! [X6,X2,X0] :
      ( r2_hidden(X6,k1_relat_1(X2))
      | ~ r2_hidden(X6,k1_relat_1(k8_relat_1(X0,X2)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(k8_relat_1(X0,X2))
      | ~ v1_relat_1(k8_relat_1(X0,X2)) ) ),
    inference(equality_resolution,[],[f3191])).

fof(f3191,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,k1_relat_1(X2))
      | ~ r2_hidden(X6,k1_relat_1(X1))
      | k8_relat_1(X0,X2) != X1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2107])).

fof(f2107,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X2) = X1
              | ( k1_funct_1(X2,sK101(X1,X2)) != k1_funct_1(X1,sK101(X1,X2))
                & r2_hidden(sK101(X1,X2),k1_relat_1(X1)) )
              | ( ( ~ r2_hidden(k1_funct_1(X2,sK102(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK102(X0,X1,X2),k1_relat_1(X2))
                  | ~ r2_hidden(sK102(X0,X1,X2),k1_relat_1(X1)) )
                & ( ( r2_hidden(k1_funct_1(X2,sK102(X0,X1,X2)),X0)
                    & r2_hidden(sK102(X0,X1,X2),k1_relat_1(X2)) )
                  | r2_hidden(sK102(X0,X1,X2),k1_relat_1(X1)) ) ) )
            & ( ( ! [X5] :
                    ( k1_funct_1(X2,X5) = k1_funct_1(X1,X5)
                    | ~ r2_hidden(X5,k1_relat_1(X1)) )
                & ! [X6] :
                    ( ( r2_hidden(X6,k1_relat_1(X1))
                      | ~ r2_hidden(k1_funct_1(X2,X6),X0)
                      | ~ r2_hidden(X6,k1_relat_1(X2)) )
                    & ( ( r2_hidden(k1_funct_1(X2,X6),X0)
                        & r2_hidden(X6,k1_relat_1(X2)) )
                      | ~ r2_hidden(X6,k1_relat_1(X1)) ) ) )
              | k8_relat_1(X0,X2) != X1 ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK101,sK102])],[f2104,f2106,f2105])).

fof(f2105,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( k1_funct_1(X2,X3) != k1_funct_1(X1,X3)
          & r2_hidden(X3,k1_relat_1(X1)) )
     => ( k1_funct_1(X2,sK101(X1,X2)) != k1_funct_1(X1,sK101(X1,X2))
        & r2_hidden(sK101(X1,X2),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2106,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ r2_hidden(k1_funct_1(X2,X4),X0)
            | ~ r2_hidden(X4,k1_relat_1(X2))
            | ~ r2_hidden(X4,k1_relat_1(X1)) )
          & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
              & r2_hidden(X4,k1_relat_1(X2)) )
            | r2_hidden(X4,k1_relat_1(X1)) ) )
     => ( ( ~ r2_hidden(k1_funct_1(X2,sK102(X0,X1,X2)),X0)
          | ~ r2_hidden(sK102(X0,X1,X2),k1_relat_1(X2))
          | ~ r2_hidden(sK102(X0,X1,X2),k1_relat_1(X1)) )
        & ( ( r2_hidden(k1_funct_1(X2,sK102(X0,X1,X2)),X0)
            & r2_hidden(sK102(X0,X1,X2),k1_relat_1(X2)) )
          | r2_hidden(sK102(X0,X1,X2),k1_relat_1(X1)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f2104,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X2) = X1
              | ? [X3] :
                  ( k1_funct_1(X2,X3) != k1_funct_1(X1,X3)
                  & r2_hidden(X3,k1_relat_1(X1)) )
              | ? [X4] :
                  ( ( ~ r2_hidden(k1_funct_1(X2,X4),X0)
                    | ~ r2_hidden(X4,k1_relat_1(X2))
                    | ~ r2_hidden(X4,k1_relat_1(X1)) )
                  & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                      & r2_hidden(X4,k1_relat_1(X2)) )
                    | r2_hidden(X4,k1_relat_1(X1)) ) ) )
            & ( ( ! [X5] :
                    ( k1_funct_1(X2,X5) = k1_funct_1(X1,X5)
                    | ~ r2_hidden(X5,k1_relat_1(X1)) )
                & ! [X6] :
                    ( ( r2_hidden(X6,k1_relat_1(X1))
                      | ~ r2_hidden(k1_funct_1(X2,X6),X0)
                      | ~ r2_hidden(X6,k1_relat_1(X2)) )
                    & ( ( r2_hidden(k1_funct_1(X2,X6),X0)
                        & r2_hidden(X6,k1_relat_1(X2)) )
                      | ~ r2_hidden(X6,k1_relat_1(X1)) ) ) )
              | k8_relat_1(X0,X2) != X1 ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f2103])).

fof(f2103,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X2) = X1
              | ? [X3] :
                  ( k1_funct_1(X2,X3) != k1_funct_1(X1,X3)
                  & r2_hidden(X3,k1_relat_1(X1)) )
              | ? [X4] :
                  ( ( ~ r2_hidden(k1_funct_1(X2,X4),X0)
                    | ~ r2_hidden(X4,k1_relat_1(X2))
                    | ~ r2_hidden(X4,k1_relat_1(X1)) )
                  & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                      & r2_hidden(X4,k1_relat_1(X2)) )
                    | r2_hidden(X4,k1_relat_1(X1)) ) ) )
            & ( ( ! [X3] :
                    ( k1_funct_1(X2,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,k1_relat_1(X1)) )
                & ! [X4] :
                    ( ( r2_hidden(X4,k1_relat_1(X1))
                      | ~ r2_hidden(k1_funct_1(X2,X4),X0)
                      | ~ r2_hidden(X4,k1_relat_1(X2)) )
                    & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                        & r2_hidden(X4,k1_relat_1(X2)) )
                      | ~ r2_hidden(X4,k1_relat_1(X1)) ) ) )
              | k8_relat_1(X0,X2) != X1 ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f2102])).

fof(f2102,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X2) = X1
              | ? [X3] :
                  ( k1_funct_1(X2,X3) != k1_funct_1(X1,X3)
                  & r2_hidden(X3,k1_relat_1(X1)) )
              | ? [X4] :
                  ( ( ~ r2_hidden(k1_funct_1(X2,X4),X0)
                    | ~ r2_hidden(X4,k1_relat_1(X2))
                    | ~ r2_hidden(X4,k1_relat_1(X1)) )
                  & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                      & r2_hidden(X4,k1_relat_1(X2)) )
                    | r2_hidden(X4,k1_relat_1(X1)) ) ) )
            & ( ( ! [X3] :
                    ( k1_funct_1(X2,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,k1_relat_1(X1)) )
                & ! [X4] :
                    ( ( r2_hidden(X4,k1_relat_1(X1))
                      | ~ r2_hidden(k1_funct_1(X2,X4),X0)
                      | ~ r2_hidden(X4,k1_relat_1(X2)) )
                    & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                        & r2_hidden(X4,k1_relat_1(X2)) )
                      | ~ r2_hidden(X4,k1_relat_1(X1)) ) ) )
              | k8_relat_1(X0,X2) != X1 ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1520])).

fof(f1520,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( k1_funct_1(X2,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1519])).

fof(f1519,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( k1_funct_1(X2,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f988])).

fof(f988,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X2,X3) = k1_funct_1(X1,X3) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) ) ) ) ),
    inference(rectify,[],[f972])).

fof(f972,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X2,X3) = k1_funct_1(X1,X3) )
              & ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X3),X0)
                    & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_1)).

fof(f5438,plain,
    ( ~ r2_hidden(sK5,k1_relat_1(sK7))
    | spl205_2 ),
    inference(avatar_component_clause,[],[f5437])).

fof(f5437,plain,
    ( spl205_2
  <=> r2_hidden(sK5,k1_relat_1(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl205_2])])).

fof(f5435,plain,
    ( r2_hidden(sK5,k1_relat_1(k8_relat_1(sK6,sK7)))
    | ~ spl205_1 ),
    inference(avatar_component_clause,[],[f5433])).

fof(f5433,plain,
    ( spl205_1
  <=> r2_hidden(sK5,k1_relat_1(k8_relat_1(sK6,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl205_1])])).

fof(f2411,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f1865])).

fof(f1865,plain,
    ( ( ~ r2_hidden(k1_funct_1(sK7,sK5),sK6)
      | ~ r2_hidden(sK5,k1_relat_1(sK7))
      | ~ r2_hidden(sK5,k1_relat_1(k8_relat_1(sK6,sK7))) )
    & ( ( r2_hidden(k1_funct_1(sK7,sK5),sK6)
        & r2_hidden(sK5,k1_relat_1(sK7)) )
      | r2_hidden(sK5,k1_relat_1(k8_relat_1(sK6,sK7))) )
    & v1_funct_1(sK7)
    & v1_relat_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f1863,f1864])).

fof(f1864,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) )
        & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
          | r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) )
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ( ~ r2_hidden(k1_funct_1(sK7,sK5),sK6)
        | ~ r2_hidden(sK5,k1_relat_1(sK7))
        | ~ r2_hidden(sK5,k1_relat_1(k8_relat_1(sK6,sK7))) )
      & ( ( r2_hidden(k1_funct_1(sK7,sK5),sK6)
          & r2_hidden(sK5,k1_relat_1(sK7)) )
        | r2_hidden(sK5,k1_relat_1(k8_relat_1(sK6,sK7))) )
      & v1_funct_1(sK7)
      & v1_relat_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f1863,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) )
      & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) )
        | r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f1862])).

fof(f1862,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) )
      & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) )
        | r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f995])).

fof(f995,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <~> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f994])).

fof(f994,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <~> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f974])).

fof(f974,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
        <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f973])).

fof(f973,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_funct_1)).

fof(f2410,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f1865])).

fof(f5658,plain,
    ( ~ spl205_1
    | ~ spl205_2 ),
    inference(avatar_contradiction_clause,[],[f5657])).

fof(f5657,plain,
    ( $false
    | ~ spl205_1
    | ~ spl205_2 ),
    inference(subsumption_resolution,[],[f5656,f5435])).

fof(f5656,plain,
    ( ~ r2_hidden(sK5,k1_relat_1(k8_relat_1(sK6,sK7)))
    | ~ spl205_1
    | ~ spl205_2 ),
    inference(subsumption_resolution,[],[f5644,f5653])).

fof(f5653,plain,
    ( r2_hidden(k1_funct_1(sK7,sK5),sK6)
    | ~ spl205_1 ),
    inference(subsumption_resolution,[],[f5652,f2410])).

fof(f5652,plain,
    ( r2_hidden(k1_funct_1(sK7,sK5),sK6)
    | ~ v1_relat_1(sK7)
    | ~ spl205_1 ),
    inference(subsumption_resolution,[],[f5645,f2411])).

fof(f5645,plain,
    ( r2_hidden(k1_funct_1(sK7,sK5),sK6)
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | ~ spl205_1 ),
    inference(resolution,[],[f5435,f5603])).

fof(f5603,plain,(
    ! [X6,X2,X0] :
      ( ~ r2_hidden(X6,k1_relat_1(k8_relat_1(X0,X2)))
      | r2_hidden(k1_funct_1(X2,X6),X0)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f5602,f2892])).

fof(f5602,plain,(
    ! [X6,X2,X0] :
      ( r2_hidden(k1_funct_1(X2,X6),X0)
      | ~ r2_hidden(X6,k1_relat_1(k8_relat_1(X0,X2)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(k8_relat_1(X0,X2)) ) ),
    inference(subsumption_resolution,[],[f4074,f3160])).

fof(f4074,plain,(
    ! [X6,X2,X0] :
      ( r2_hidden(k1_funct_1(X2,X6),X0)
      | ~ r2_hidden(X6,k1_relat_1(k8_relat_1(X0,X2)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(k8_relat_1(X0,X2))
      | ~ v1_relat_1(k8_relat_1(X0,X2)) ) ),
    inference(equality_resolution,[],[f3192])).

fof(f3192,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X2,X6),X0)
      | ~ r2_hidden(X6,k1_relat_1(X1))
      | k8_relat_1(X0,X2) != X1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2107])).

fof(f5644,plain,
    ( ~ r2_hidden(k1_funct_1(sK7,sK5),sK6)
    | ~ r2_hidden(sK5,k1_relat_1(k8_relat_1(sK6,sK7)))
    | ~ spl205_2 ),
    inference(subsumption_resolution,[],[f2414,f5439])).

fof(f5439,plain,
    ( r2_hidden(sK5,k1_relat_1(sK7))
    | ~ spl205_2 ),
    inference(avatar_component_clause,[],[f5437])).

fof(f2414,plain,
    ( ~ r2_hidden(k1_funct_1(sK7,sK5),sK6)
    | ~ r2_hidden(sK5,k1_relat_1(sK7))
    | ~ r2_hidden(sK5,k1_relat_1(k8_relat_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f1865])).

fof(f5635,plain,
    ( spl205_1
    | ~ spl205_2 ),
    inference(avatar_contradiction_clause,[],[f5629])).

fof(f5629,plain,
    ( $false
    | spl205_1
    | ~ spl205_2 ),
    inference(unit_resulting_resolution,[],[f2410,f2411,f5439,f5441,f5434,f5628])).

fof(f5628,plain,(
    ! [X6,X2,X0] :
      ( ~ r2_hidden(X6,k1_relat_1(X2))
      | ~ r2_hidden(k1_funct_1(X2,X6),X0)
      | r2_hidden(X6,k1_relat_1(k8_relat_1(X0,X2)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f5627,f2892])).

fof(f5627,plain,(
    ! [X6,X2,X0] :
      ( r2_hidden(X6,k1_relat_1(k8_relat_1(X0,X2)))
      | ~ r2_hidden(k1_funct_1(X2,X6),X0)
      | ~ r2_hidden(X6,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(k8_relat_1(X0,X2)) ) ),
    inference(subsumption_resolution,[],[f4073,f3160])).

fof(f4073,plain,(
    ! [X6,X2,X0] :
      ( r2_hidden(X6,k1_relat_1(k8_relat_1(X0,X2)))
      | ~ r2_hidden(k1_funct_1(X2,X6),X0)
      | ~ r2_hidden(X6,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(k8_relat_1(X0,X2))
      | ~ v1_relat_1(k8_relat_1(X0,X2)) ) ),
    inference(equality_resolution,[],[f3193])).

fof(f3193,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,k1_relat_1(X1))
      | ~ r2_hidden(k1_funct_1(X2,X6),X0)
      | ~ r2_hidden(X6,k1_relat_1(X2))
      | k8_relat_1(X0,X2) != X1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2107])).

fof(f5434,plain,
    ( ~ r2_hidden(sK5,k1_relat_1(k8_relat_1(sK6,sK7)))
    | spl205_1 ),
    inference(avatar_component_clause,[],[f5433])).

fof(f5441,plain,
    ( r2_hidden(k1_funct_1(sK7,sK5),sK6)
    | spl205_1 ),
    inference(subsumption_resolution,[],[f2413,f5434])).

fof(f2413,plain,
    ( r2_hidden(k1_funct_1(sK7,sK5),sK6)
    | r2_hidden(sK5,k1_relat_1(k8_relat_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f1865])).

fof(f5440,plain,
    ( spl205_1
    | spl205_2 ),
    inference(avatar_split_clause,[],[f2412,f5437,f5433])).

fof(f2412,plain,
    ( r2_hidden(sK5,k1_relat_1(sK7))
    | r2_hidden(sK5,k1_relat_1(k8_relat_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f1865])).
%------------------------------------------------------------------------------
