%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:33 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 608 expanded)
%              Number of leaves         :   14 ( 210 expanded)
%              Depth                    :   15
%              Number of atoms          :  416 (5269 expanded)
%              Number of equality atoms :   69 (1589 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f142,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f95,f135,f141])).

% (20441)Termination reason: Refutation not found, incomplete strategy

% (20441)Memory used [KB]: 10746
% (20441)Time elapsed: 0.111 s
% (20441)------------------------------
% (20441)------------------------------
fof(f141,plain,
    ( ~ spl8_1
    | spl8_3 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | ~ spl8_1
    | spl8_3 ),
    inference(subsumption_resolution,[],[f139,f138])).

fof(f138,plain,
    ( r2_hidden(k1_funct_1(sK2,sK4(sK0,sK1,sK2)),k2_relat_1(sK2))
    | ~ spl8_1
    | spl8_3 ),
    inference(unit_resulting_resolution,[],[f137,f110])).

fof(f110,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f109,f94])).

fof(f94,plain,(
    v1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f79,f81])).

fof(f81,plain,(
    sK2 = sK7(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f27,f63])).

fof(f63,plain,(
    ! [X6,X0,X1] :
      ( sK7(X0,X1,X6) = X6
      | ~ r2_hidden(X6,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X6,X2,X0,X1] :
      ( sK7(X0,X1,X6) = X6
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X1)
                | k1_relat_1(X4) != X0
                | sK5(X0,X1,X2) != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( r1_tarski(k2_relat_1(sK6(X0,X1,X2)),X1)
              & k1_relat_1(sK6(X0,X1,X2)) = X0
              & sK5(X0,X1,X2) = sK6(X0,X1,X2)
              & v1_funct_1(sK6(X0,X1,X2))
              & v1_relat_1(sK6(X0,X1,X2)) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X1)
                  | k1_relat_1(X7) != X0
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ( r1_tarski(k2_relat_1(sK7(X0,X1,X6)),X1)
                & k1_relat_1(sK7(X0,X1,X6)) = X0
                & sK7(X0,X1,X6) = X6
                & v1_funct_1(sK7(X0,X1,X6))
                & v1_relat_1(sK7(X0,X1,X6)) )
              | ~ r2_hidden(X6,X2) ) )
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f22,f25,f24,f23])).

fof(f23,plain,(
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
              | sK5(X0,X1,X2) != X4
              | ~ v1_funct_1(X4)
              | ~ v1_relat_1(X4) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r1_tarski(k2_relat_1(X5),X1)
              & k1_relat_1(X5) = X0
              & sK5(X0,X1,X2) = X5
              & v1_funct_1(X5)
              & v1_relat_1(X5) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r1_tarski(k2_relat_1(X5),X1)
          & k1_relat_1(X5) = X0
          & sK5(X0,X1,X2) = X5
          & v1_funct_1(X5)
          & v1_relat_1(X5) )
     => ( r1_tarski(k2_relat_1(sK6(X0,X1,X2)),X1)
        & k1_relat_1(sK6(X0,X1,X2)) = X0
        & sK5(X0,X1,X2) = sK6(X0,X1,X2)
        & v1_funct_1(sK6(X0,X1,X2))
        & v1_relat_1(sK6(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r1_tarski(k2_relat_1(X8),X1)
          & k1_relat_1(X8) = X0
          & X6 = X8
          & v1_funct_1(X8)
          & v1_relat_1(X8) )
     => ( r1_tarski(k2_relat_1(sK7(X0,X1,X6)),X1)
        & k1_relat_1(sK7(X0,X1,X6)) = X0
        & sK7(X0,X1,X6) = X6
        & v1_funct_1(sK7(X0,X1,X6))
        & v1_relat_1(sK7(X0,X1,X6)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).

fof(f27,plain,(
    r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) )
    & r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2) )
        & r2_hidden(X2,k1_funct_2(X0,X1)) )
   => ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
      & r2_hidden(sK2,k1_funct_2(sK0,sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

fof(f79,plain,(
    v1_relat_1(sK7(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f27,f65])).

fof(f65,plain,(
    ! [X6,X0,X1] :
      ( v1_relat_1(sK7(X0,X1,X6))
      | ~ r2_hidden(X6,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_relat_1(sK7(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f109,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2))
        | ~ v1_relat_1(sK2) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f96,f68])).

fof(f68,plain,
    ( v1_funct_1(sK2)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl8_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f96,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f29,f89])).

fof(f89,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f82,f81])).

fof(f82,plain,(
    sK0 = k1_relat_1(sK7(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f27,f62])).

fof(f62,plain,(
    ! [X6,X0,X1] :
      ( k1_relat_1(sK7(X0,X1,X6)) = X0
      | ~ r2_hidden(X6,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_relat_1(sK7(X0,X1,X6)) = X0
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
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

fof(f137,plain,
    ( r2_hidden(sK4(sK0,sK1,sK2),sK0)
    | ~ spl8_1
    | spl8_3 ),
    inference(unit_resulting_resolution,[],[f77,f114])).

fof(f114,plain,
    ( ! [X3] :
        ( r2_hidden(sK4(sK0,X3,sK2),sK0)
        | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X3))) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f113,f94])).

fof(f113,plain,
    ( ! [X3] :
        ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X3)))
        | r2_hidden(sK4(sK0,X3,sK2),sK0)
        | ~ v1_relat_1(sK2) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f99,f68])).

fof(f99,plain,(
    ! [X3] :
      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X3)))
      | r2_hidden(sK4(sK0,X3,sK2),sK0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f52,f89])).

fof(f52,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | r2_hidden(sK4(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK4(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ( ~ r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1)
        & r2_hidden(sK4(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f19])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1)
        & r2_hidden(sK4(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( ! [X3] :
              ( r2_hidden(X3,X0)
             => r2_hidden(k1_funct_1(X2,X3),X1) )
          & k1_relat_1(X2) = X0 )
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).

fof(f77,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl8_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl8_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f139,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK4(sK0,sK1,sK2)),k2_relat_1(sK2))
    | ~ spl8_1
    | spl8_3 ),
    inference(unit_resulting_resolution,[],[f90,f136,f30])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f136,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ spl8_1
    | spl8_3 ),
    inference(unit_resulting_resolution,[],[f77,f112])).

fof(f112,plain,
    ( ! [X1] :
        ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ r2_hidden(k1_funct_1(sK2,sK4(sK0,X1,sK2)),X1) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f111,f94])).

fof(f111,plain,
    ( ! [X1] :
        ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ r2_hidden(k1_funct_1(sK2,sK4(sK0,X1,sK2)),X1)
        | ~ v1_relat_1(sK2) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f97,f68])).

fof(f97,plain,(
    ! [X1] :
      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
      | ~ r2_hidden(k1_funct_1(sK2,sK4(sK0,X1,sK2)),X1)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f51,f89])).

fof(f51,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK4(k1_relat_1(X2),X1,X2)),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f90,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(backward_demodulation,[],[f83,f81])).

fof(f83,plain,(
    r1_tarski(k2_relat_1(sK7(sK0,sK1,sK2)),sK1) ),
    inference(unit_resulting_resolution,[],[f27,f61])).

fof(f61,plain,(
    ! [X6,X0,X1] :
      ( r1_tarski(k2_relat_1(sK7(X0,X1,X6)),X1)
      | ~ r2_hidden(X6,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_tarski(k2_relat_1(sK7(X0,X1,X6)),X1)
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f135,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | ~ spl8_1
    | spl8_2 ),
    inference(subsumption_resolution,[],[f133,f132])).

fof(f132,plain,
    ( r2_hidden(k1_funct_1(sK2,sK4(sK0,sK1,sK2)),k2_relat_1(sK2))
    | ~ spl8_1
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f130,f110])).

fof(f130,plain,
    ( r2_hidden(sK4(sK0,sK1,sK2),sK0)
    | ~ spl8_1
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f73,f118])).

fof(f118,plain,
    ( ! [X7] :
        ( v1_funct_2(sK2,sK0,X7)
        | r2_hidden(sK4(sK0,X7,sK2),sK0) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f117,f94])).

fof(f117,plain,
    ( ! [X7] :
        ( r2_hidden(sK4(sK0,X7,sK2),sK0)
        | v1_funct_2(sK2,sK0,X7)
        | ~ v1_relat_1(sK2) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f103,f68])).

fof(f103,plain,(
    ! [X7] :
      ( r2_hidden(sK4(sK0,X7,sK2),sK0)
      | v1_funct_2(sK2,sK0,X7)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f54,f89])).

fof(f54,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_relat_1(X2),X1)
      | r2_hidden(sK4(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f73,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl8_2
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f133,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK4(sK0,sK1,sK2)),k2_relat_1(sK2))
    | ~ spl8_1
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f90,f131,f30])).

fof(f131,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK4(sK0,sK1,sK2)),sK1)
    | ~ spl8_1
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f73,f116])).

fof(f116,plain,
    ( ! [X5] :
        ( v1_funct_2(sK2,sK0,X5)
        | ~ r2_hidden(k1_funct_1(sK2,sK4(sK0,X5,sK2)),X5) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f115,f94])).

fof(f115,plain,
    ( ! [X5] :
        ( ~ r2_hidden(k1_funct_1(sK2,sK4(sK0,X5,sK2)),X5)
        | v1_funct_2(sK2,sK0,X5)
        | ~ v1_relat_1(sK2) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f101,f68])).

fof(f101,plain,(
    ! [X5] :
      ( ~ r2_hidden(k1_funct_1(sK2,sK4(sK0,X5,sK2)),X5)
      | v1_funct_2(sK2,sK0,X5)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f53,f89])).

fof(f53,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_relat_1(X2),X1)
      | ~ r2_hidden(k1_funct_1(X2,sK4(k1_relat_1(X2),X1,X2)),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f95,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f91,f67])).

fof(f91,plain,(
    v1_funct_1(sK2) ),
    inference(forward_demodulation,[],[f80,f81])).

fof(f80,plain,(
    v1_funct_1(sK7(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f27,f64])).

fof(f64,plain,(
    ! [X6,X0,X1] :
      ( v1_funct_1(sK7(X0,X1,X6))
      | ~ r2_hidden(X6,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_funct_1(sK7(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f78,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f28,f75,f71,f67])).

fof(f28,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:05:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (20437)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (20457)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.51  % (20450)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.51  % (20441)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.51  % (20452)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.52  % (20441)Refutation not found, incomplete strategy% (20441)------------------------------
% 0.22/0.52  % (20441)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (20457)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (20445)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (20447)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f142,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f78,f95,f135,f141])).
% 0.22/0.53  % (20441)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (20441)Memory used [KB]: 10746
% 0.22/0.53  % (20441)Time elapsed: 0.111 s
% 0.22/0.53  % (20441)------------------------------
% 0.22/0.53  % (20441)------------------------------
% 0.22/0.53  fof(f141,plain,(
% 0.22/0.53    ~spl8_1 | spl8_3),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f140])).
% 0.22/0.53  fof(f140,plain,(
% 0.22/0.53    $false | (~spl8_1 | spl8_3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f139,f138])).
% 0.22/0.53  fof(f138,plain,(
% 0.22/0.53    r2_hidden(k1_funct_1(sK2,sK4(sK0,sK1,sK2)),k2_relat_1(sK2)) | (~spl8_1 | spl8_3)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f137,f110])).
% 0.22/0.53  fof(f110,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2))) ) | ~spl8_1),
% 0.22/0.53    inference(subsumption_resolution,[],[f109,f94])).
% 0.22/0.53  fof(f94,plain,(
% 0.22/0.53    v1_relat_1(sK2)),
% 0.22/0.53    inference(forward_demodulation,[],[f79,f81])).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    sK2 = sK7(sK0,sK1,sK2)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f27,f63])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    ( ! [X6,X0,X1] : (sK7(X0,X1,X6) = X6 | ~r2_hidden(X6,k1_funct_2(X0,X1))) )),
% 0.22/0.53    inference(equality_resolution,[],[f41])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ( ! [X6,X2,X0,X1] : (sK7(X0,X1,X6) = X6 | ~r2_hidden(X6,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | sK5(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r1_tarski(k2_relat_1(sK6(X0,X1,X2)),X1) & k1_relat_1(sK6(X0,X1,X2)) = X0 & sK5(X0,X1,X2) = sK6(X0,X1,X2) & v1_funct_1(sK6(X0,X1,X2)) & v1_relat_1(sK6(X0,X1,X2))) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X1) | k1_relat_1(X7) != X0 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & ((r1_tarski(k2_relat_1(sK7(X0,X1,X6)),X1) & k1_relat_1(sK7(X0,X1,X6)) = X0 & sK7(X0,X1,X6) = X6 & v1_funct_1(sK7(X0,X1,X6)) & v1_relat_1(sK7(X0,X1,X6))) | ~r2_hidden(X6,X2))) | k1_funct_2(X0,X1) != X2))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f22,f25,f24,f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X1) & k1_relat_1(X5) = X0 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2))) => ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | sK5(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X1) & k1_relat_1(X5) = X0 & sK5(X0,X1,X2) = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X2,X1,X0] : (? [X5] : (r1_tarski(k2_relat_1(X5),X1) & k1_relat_1(X5) = X0 & sK5(X0,X1,X2) = X5 & v1_funct_1(X5) & v1_relat_1(X5)) => (r1_tarski(k2_relat_1(sK6(X0,X1,X2)),X1) & k1_relat_1(sK6(X0,X1,X2)) = X0 & sK5(X0,X1,X2) = sK6(X0,X1,X2) & v1_funct_1(sK6(X0,X1,X2)) & v1_relat_1(sK6(X0,X1,X2))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X6,X1,X0] : (? [X8] : (r1_tarski(k2_relat_1(X8),X1) & k1_relat_1(X8) = X0 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) => (r1_tarski(k2_relat_1(sK7(X0,X1,X6)),X1) & k1_relat_1(sK7(X0,X1,X6)) = X0 & sK7(X0,X1,X6) = X6 & v1_funct_1(sK7(X0,X1,X6)) & v1_relat_1(sK7(X0,X1,X6))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X1) & k1_relat_1(X5) = X0 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X1) | k1_relat_1(X7) != X0 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & (? [X8] : (r1_tarski(k2_relat_1(X8),X1) & k1_relat_1(X8) = X0 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) | ~r2_hidden(X6,X2))) | k1_funct_2(X0,X1) != X2))),
% 0.22/0.53    inference(rectify,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4))) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | ~r2_hidden(X3,X2))) | k1_funct_2(X0,X1) != X2))),
% 0.22/0.53    inference(nnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    r2_hidden(sK2,k1_funct_2(sK0,sK1))),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) & r2_hidden(sK2,k1_funct_2(sK0,sK1))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1))) => ((~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) & r2_hidden(sK2,k1_funct_2(sK0,sK1)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f7,plain,(
% 0.22/0.53    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.53    inference(negated_conjecture,[],[f5])).
% 0.22/0.53  fof(f5,conjecture,(
% 0.22/0.53    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    v1_relat_1(sK7(sK0,sK1,sK2))),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f27,f65])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    ( ! [X6,X0,X1] : (v1_relat_1(sK7(X0,X1,X6)) | ~r2_hidden(X6,k1_funct_2(X0,X1))) )),
% 0.22/0.53    inference(equality_resolution,[],[f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ( ! [X6,X2,X0,X1] : (v1_relat_1(sK7(X0,X1,X6)) | ~r2_hidden(X6,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f109,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)) | ~v1_relat_1(sK2)) ) | ~spl8_1),
% 0.22/0.53    inference(subsumption_resolution,[],[f96,f68])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    v1_funct_1(sK2) | ~spl8_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f67])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    spl8_1 <=> v1_funct_1(sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.22/0.53  fof(f96,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.22/0.53    inference(superposition,[],[f29,f89])).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    sK0 = k1_relat_1(sK2)),
% 0.22/0.53    inference(backward_demodulation,[],[f82,f81])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    sK0 = k1_relat_1(sK7(sK0,sK1,sK2))),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f27,f62])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    ( ! [X6,X0,X1] : (k1_relat_1(sK7(X0,X1,X6)) = X0 | ~r2_hidden(X6,k1_funct_2(X0,X1))) )),
% 0.22/0.53    inference(equality_resolution,[],[f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ( ! [X6,X2,X0,X1] : (k1_relat_1(sK7(X0,X1,X6)) = X0 | ~r2_hidden(X6,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,plain,(
% 0.22/0.53    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(flattening,[],[f8])).
% 0.22/0.53  fof(f8,plain,(
% 0.22/0.53    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).
% 0.22/0.53  fof(f137,plain,(
% 0.22/0.53    r2_hidden(sK4(sK0,sK1,sK2),sK0) | (~spl8_1 | spl8_3)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f77,f114])).
% 0.22/0.53  fof(f114,plain,(
% 0.22/0.53    ( ! [X3] : (r2_hidden(sK4(sK0,X3,sK2),sK0) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X3)))) ) | ~spl8_1),
% 0.22/0.53    inference(subsumption_resolution,[],[f113,f94])).
% 0.22/0.53  fof(f113,plain,(
% 0.22/0.53    ( ! [X3] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X3))) | r2_hidden(sK4(sK0,X3,sK2),sK0) | ~v1_relat_1(sK2)) ) | ~spl8_1),
% 0.22/0.53    inference(subsumption_resolution,[],[f99,f68])).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    ( ! [X3] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X3))) | r2_hidden(sK4(sK0,X3,sK2),sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.22/0.53    inference(superposition,[],[f52,f89])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | r2_hidden(sK4(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.53    inference(equality_resolution,[],[f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(sK4(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1) & r2_hidden(sK4(X0,X1,X2),X0)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.53    inference(flattening,[],[f11])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl8_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f75])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    spl8_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.22/0.53  fof(f139,plain,(
% 0.22/0.53    ~r2_hidden(k1_funct_1(sK2,sK4(sK0,sK1,sK2)),k2_relat_1(sK2)) | (~spl8_1 | spl8_3)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f90,f136,f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.53    inference(rectify,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.53    inference(nnf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,plain,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.53  fof(f136,plain,(
% 0.22/0.53    ~r2_hidden(k1_funct_1(sK2,sK4(sK0,sK1,sK2)),sK1) | (~spl8_1 | spl8_3)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f77,f112])).
% 0.22/0.53  fof(f112,plain,(
% 0.22/0.53    ( ! [X1] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~r2_hidden(k1_funct_1(sK2,sK4(sK0,X1,sK2)),X1)) ) | ~spl8_1),
% 0.22/0.53    inference(subsumption_resolution,[],[f111,f94])).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    ( ! [X1] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~r2_hidden(k1_funct_1(sK2,sK4(sK0,X1,sK2)),X1) | ~v1_relat_1(sK2)) ) | ~spl8_1),
% 0.22/0.53    inference(subsumption_resolution,[],[f97,f68])).
% 0.22/0.53  fof(f97,plain,(
% 0.22/0.53    ( ! [X1] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~r2_hidden(k1_funct_1(sK2,sK4(sK0,X1,sK2)),X1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.22/0.53    inference(superposition,[],[f51,f89])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | ~r2_hidden(k1_funct_1(X2,sK4(k1_relat_1(X2),X1,X2)),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.53    inference(equality_resolution,[],[f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f90,plain,(
% 0.22/0.53    r1_tarski(k2_relat_1(sK2),sK1)),
% 0.22/0.53    inference(backward_demodulation,[],[f83,f81])).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    r1_tarski(k2_relat_1(sK7(sK0,sK1,sK2)),sK1)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f27,f61])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    ( ! [X6,X0,X1] : (r1_tarski(k2_relat_1(sK7(X0,X1,X6)),X1) | ~r2_hidden(X6,k1_funct_2(X0,X1))) )),
% 0.22/0.53    inference(equality_resolution,[],[f43])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ( ! [X6,X2,X0,X1] : (r1_tarski(k2_relat_1(sK7(X0,X1,X6)),X1) | ~r2_hidden(X6,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f135,plain,(
% 0.22/0.53    ~spl8_1 | spl8_2),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f134])).
% 0.22/0.53  fof(f134,plain,(
% 0.22/0.53    $false | (~spl8_1 | spl8_2)),
% 0.22/0.53    inference(subsumption_resolution,[],[f133,f132])).
% 0.22/0.53  fof(f132,plain,(
% 0.22/0.53    r2_hidden(k1_funct_1(sK2,sK4(sK0,sK1,sK2)),k2_relat_1(sK2)) | (~spl8_1 | spl8_2)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f130,f110])).
% 0.22/0.53  fof(f130,plain,(
% 0.22/0.53    r2_hidden(sK4(sK0,sK1,sK2),sK0) | (~spl8_1 | spl8_2)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f73,f118])).
% 0.22/0.53  fof(f118,plain,(
% 0.22/0.53    ( ! [X7] : (v1_funct_2(sK2,sK0,X7) | r2_hidden(sK4(sK0,X7,sK2),sK0)) ) | ~spl8_1),
% 0.22/0.53    inference(subsumption_resolution,[],[f117,f94])).
% 0.22/0.53  fof(f117,plain,(
% 0.22/0.53    ( ! [X7] : (r2_hidden(sK4(sK0,X7,sK2),sK0) | v1_funct_2(sK2,sK0,X7) | ~v1_relat_1(sK2)) ) | ~spl8_1),
% 0.22/0.53    inference(subsumption_resolution,[],[f103,f68])).
% 0.22/0.53  fof(f103,plain,(
% 0.22/0.53    ( ! [X7] : (r2_hidden(sK4(sK0,X7,sK2),sK0) | v1_funct_2(sK2,sK0,X7) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.22/0.53    inference(superposition,[],[f54,f89])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ( ! [X2,X1] : (v1_funct_2(X2,k1_relat_1(X2),X1) | r2_hidden(sK4(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.53    inference(equality_resolution,[],[f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | r2_hidden(sK4(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    ~v1_funct_2(sK2,sK0,sK1) | spl8_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f71])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    spl8_2 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.22/0.53  fof(f133,plain,(
% 0.22/0.53    ~r2_hidden(k1_funct_1(sK2,sK4(sK0,sK1,sK2)),k2_relat_1(sK2)) | (~spl8_1 | spl8_2)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f90,f131,f30])).
% 0.22/0.53  fof(f131,plain,(
% 0.22/0.53    ~r2_hidden(k1_funct_1(sK2,sK4(sK0,sK1,sK2)),sK1) | (~spl8_1 | spl8_2)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f73,f116])).
% 0.22/0.53  fof(f116,plain,(
% 0.22/0.53    ( ! [X5] : (v1_funct_2(sK2,sK0,X5) | ~r2_hidden(k1_funct_1(sK2,sK4(sK0,X5,sK2)),X5)) ) | ~spl8_1),
% 0.22/0.53    inference(subsumption_resolution,[],[f115,f94])).
% 0.22/0.53  fof(f115,plain,(
% 0.22/0.53    ( ! [X5] : (~r2_hidden(k1_funct_1(sK2,sK4(sK0,X5,sK2)),X5) | v1_funct_2(sK2,sK0,X5) | ~v1_relat_1(sK2)) ) | ~spl8_1),
% 0.22/0.53    inference(subsumption_resolution,[],[f101,f68])).
% 0.22/0.53  fof(f101,plain,(
% 0.22/0.53    ( ! [X5] : (~r2_hidden(k1_funct_1(sK2,sK4(sK0,X5,sK2)),X5) | v1_funct_2(sK2,sK0,X5) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.22/0.53    inference(superposition,[],[f53,f89])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ( ! [X2,X1] : (v1_funct_2(X2,k1_relat_1(X2),X1) | ~r2_hidden(k1_funct_1(X2,sK4(k1_relat_1(X2),X1,X2)),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.53    inference(equality_resolution,[],[f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f95,plain,(
% 0.22/0.53    spl8_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f91,f67])).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    v1_funct_1(sK2)),
% 0.22/0.53    inference(forward_demodulation,[],[f80,f81])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    v1_funct_1(sK7(sK0,sK1,sK2))),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f27,f64])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    ( ! [X6,X0,X1] : (v1_funct_1(sK7(X0,X1,X6)) | ~r2_hidden(X6,k1_funct_2(X0,X1))) )),
% 0.22/0.53    inference(equality_resolution,[],[f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ( ! [X6,X2,X0,X1] : (v1_funct_1(sK7(X0,X1,X6)) | ~r2_hidden(X6,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    ~spl8_1 | ~spl8_2 | ~spl8_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f28,f75,f71,f67])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (20457)------------------------------
% 0.22/0.53  % (20457)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (20457)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (20457)Memory used [KB]: 10746
% 0.22/0.53  % (20457)Time elapsed: 0.122 s
% 0.22/0.53  % (20457)------------------------------
% 0.22/0.53  % (20457)------------------------------
% 0.22/0.53  % (20430)Success in time 0.171 s
%------------------------------------------------------------------------------
