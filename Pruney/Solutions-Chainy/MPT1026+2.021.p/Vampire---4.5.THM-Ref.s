%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 336 expanded)
%              Number of leaves         :   10 ( 118 expanded)
%              Depth                    :   14
%              Number of atoms          :  256 (3005 expanded)
%              Number of equality atoms :   61 ( 935 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f125,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f107,f116,f124])).

fof(f124,plain,(
    spl6_3 ),
    inference(avatar_contradiction_clause,[],[f123])).

fof(f123,plain,
    ( $false
    | spl6_3 ),
    inference(subsumption_resolution,[],[f122,f53])).

fof(f53,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl6_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f122,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f121,f62])).

fof(f62,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f61,f58])).

fof(f58,plain,(
    sK2 = sK5(sK0,sK1,sK2) ),
    inference(resolution,[],[f39,f16])).

fof(f16,plain,(
    r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) )
    & r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f8])).

fof(f8,plain,
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

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

fof(f39,plain,(
    ! [X6,X0,X1] :
      ( ~ r2_hidden(X6,k1_funct_2(X0,X1))
      | sK5(X0,X1,X6) = X6 ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X6,X2,X0,X1] :
      ( sK5(X0,X1,X6) = X6
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X1)
                | k1_relat_1(X4) != X0
                | sK3(X0,X1,X2) != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r1_tarski(k2_relat_1(sK4(X0,X1,X2)),X1)
              & k1_relat_1(sK4(X0,X1,X2)) = X0
              & sK3(X0,X1,X2) = sK4(X0,X1,X2)
              & v1_funct_1(sK4(X0,X1,X2))
              & v1_relat_1(sK4(X0,X1,X2)) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X1)
                  | k1_relat_1(X7) != X0
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ( r1_tarski(k2_relat_1(sK5(X0,X1,X6)),X1)
                & k1_relat_1(sK5(X0,X1,X6)) = X0
                & sK5(X0,X1,X6) = X6
                & v1_funct_1(sK5(X0,X1,X6))
                & v1_relat_1(sK5(X0,X1,X6)) )
              | ~ r2_hidden(X6,X2) ) )
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f11,f14,f13,f12])).

fof(f12,plain,(
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
              | sK3(X0,X1,X2) != X4
              | ~ v1_funct_1(X4)
              | ~ v1_relat_1(X4) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r1_tarski(k2_relat_1(X5),X1)
              & k1_relat_1(X5) = X0
              & sK3(X0,X1,X2) = X5
              & v1_funct_1(X5)
              & v1_relat_1(X5) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r1_tarski(k2_relat_1(X5),X1)
          & k1_relat_1(X5) = X0
          & sK3(X0,X1,X2) = X5
          & v1_funct_1(X5)
          & v1_relat_1(X5) )
     => ( r1_tarski(k2_relat_1(sK4(X0,X1,X2)),X1)
        & k1_relat_1(sK4(X0,X1,X2)) = X0
        & sK3(X0,X1,X2) = sK4(X0,X1,X2)
        & v1_funct_1(sK4(X0,X1,X2))
        & v1_relat_1(sK4(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r1_tarski(k2_relat_1(X8),X1)
          & k1_relat_1(X8) = X0
          & X6 = X8
          & v1_funct_1(X8)
          & v1_relat_1(X8) )
     => ( r1_tarski(k2_relat_1(sK5(X0,X1,X6)),X1)
        & k1_relat_1(sK5(X0,X1,X6)) = X0
        & sK5(X0,X1,X6) = X6
        & v1_funct_1(sK5(X0,X1,X6))
        & v1_relat_1(sK5(X0,X1,X6)) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
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
    inference(rectify,[],[f10])).

fof(f10,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f61,plain,(
    sK0 = k1_relat_1(sK5(sK0,sK1,sK2)) ),
    inference(resolution,[],[f38,f16])).

fof(f38,plain,(
    ! [X6,X0,X1] :
      ( ~ r2_hidden(X6,k1_funct_2(X0,X1))
      | k1_relat_1(sK5(X0,X1,X6)) = X0 ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_relat_1(sK5(X0,X1,X6)) = X0
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f121,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) ),
    inference(subsumption_resolution,[],[f120,f104])).

fof(f104,plain,(
    v1_relat_1(sK2) ),
    inference(superposition,[],[f57,f58])).

fof(f57,plain,(
    v1_relat_1(sK5(sK0,sK1,sK2)) ),
    inference(resolution,[],[f41,f16])).

fof(f41,plain,(
    ! [X6,X0,X1] :
      ( ~ r2_hidden(X6,k1_funct_2(X0,X1))
      | v1_relat_1(sK5(X0,X1,X6)) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_relat_1(sK5(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f120,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f63,f105])).

fof(f105,plain,(
    v1_funct_1(sK2) ),
    inference(superposition,[],[f56,f58])).

fof(f56,plain,(
    v1_funct_1(sK5(sK0,sK1,sK2)) ),
    inference(resolution,[],[f40,f16])).

fof(f40,plain,(
    ! [X6,X0,X1] :
      ( ~ r2_hidden(X6,k1_funct_2(X0,X1))
      | v1_funct_1(sK5(X0,X1,X6)) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_funct_1(sK5(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f63,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f60,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f60,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(forward_demodulation,[],[f59,f58])).

fof(f59,plain,(
    r1_tarski(k2_relat_1(sK5(sK0,sK1,sK2)),sK1) ),
    inference(resolution,[],[f37,f16])).

fof(f37,plain,(
    ! [X6,X0,X1] :
      ( ~ r2_hidden(X6,k1_funct_2(X0,X1))
      | r1_tarski(k2_relat_1(sK5(X0,X1,X6)),X1) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_tarski(k2_relat_1(sK5(X0,X1,X6)),X1)
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f116,plain,(
    spl6_2 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | spl6_2 ),
    inference(subsumption_resolution,[],[f114,f49])).

fof(f49,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl6_2
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f114,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(forward_demodulation,[],[f113,f62])).

fof(f113,plain,(
    v1_funct_2(sK2,k1_relat_1(sK2),sK1) ),
    inference(subsumption_resolution,[],[f112,f104])).

fof(f112,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f65,f105])).

fof(f65,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f60,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f107,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f106])).

fof(f106,plain,
    ( $false
    | spl6_1 ),
    inference(subsumption_resolution,[],[f105,f45])).

fof(f45,plain,
    ( ~ v1_funct_1(sK2)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl6_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f54,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f17,f51,f47,f43])).

fof(f17,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:42:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (16702)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.46  % (16694)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.46  % (16694)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f125,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f54,f107,f116,f124])).
% 0.21/0.46  fof(f124,plain,(
% 0.21/0.46    spl6_3),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f123])).
% 0.21/0.46  fof(f123,plain,(
% 0.21/0.46    $false | spl6_3),
% 0.21/0.46    inference(subsumption_resolution,[],[f122,f53])).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl6_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f51])).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    spl6_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.46  fof(f122,plain,(
% 0.21/0.46    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.46    inference(forward_demodulation,[],[f121,f62])).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    sK0 = k1_relat_1(sK2)),
% 0.21/0.46    inference(forward_demodulation,[],[f61,f58])).
% 0.21/0.46  fof(f58,plain,(
% 0.21/0.46    sK2 = sK5(sK0,sK1,sK2)),
% 0.21/0.46    inference(resolution,[],[f39,f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    r2_hidden(sK2,k1_funct_2(sK0,sK1))),
% 0.21/0.46    inference(cnf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) & r2_hidden(sK2,k1_funct_2(sK0,sK1))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f8])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1))) => ((~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) & r2_hidden(sK2,k1_funct_2(sK0,sK1)))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f5,plain,(
% 0.21/0.46    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.46    inference(negated_conjecture,[],[f3])).
% 0.21/0.46  fof(f3,conjecture,(
% 0.21/0.46    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    ( ! [X6,X0,X1] : (~r2_hidden(X6,k1_funct_2(X0,X1)) | sK5(X0,X1,X6) = X6) )),
% 0.21/0.46    inference(equality_resolution,[],[f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ( ! [X6,X2,X0,X1] : (sK5(X0,X1,X6) = X6 | ~r2_hidden(X6,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | sK3(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r1_tarski(k2_relat_1(sK4(X0,X1,X2)),X1) & k1_relat_1(sK4(X0,X1,X2)) = X0 & sK3(X0,X1,X2) = sK4(X0,X1,X2) & v1_funct_1(sK4(X0,X1,X2)) & v1_relat_1(sK4(X0,X1,X2))) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X1) | k1_relat_1(X7) != X0 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & ((r1_tarski(k2_relat_1(sK5(X0,X1,X6)),X1) & k1_relat_1(sK5(X0,X1,X6)) = X0 & sK5(X0,X1,X6) = X6 & v1_funct_1(sK5(X0,X1,X6)) & v1_relat_1(sK5(X0,X1,X6))) | ~r2_hidden(X6,X2))) | k1_funct_2(X0,X1) != X2))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f11,f14,f13,f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X1) & k1_relat_1(X5) = X0 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2))) => ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | sK3(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X1) & k1_relat_1(X5) = X0 & sK3(X0,X1,X2) = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ! [X2,X1,X0] : (? [X5] : (r1_tarski(k2_relat_1(X5),X1) & k1_relat_1(X5) = X0 & sK3(X0,X1,X2) = X5 & v1_funct_1(X5) & v1_relat_1(X5)) => (r1_tarski(k2_relat_1(sK4(X0,X1,X2)),X1) & k1_relat_1(sK4(X0,X1,X2)) = X0 & sK3(X0,X1,X2) = sK4(X0,X1,X2) & v1_funct_1(sK4(X0,X1,X2)) & v1_relat_1(sK4(X0,X1,X2))))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ! [X6,X1,X0] : (? [X8] : (r1_tarski(k2_relat_1(X8),X1) & k1_relat_1(X8) = X0 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) => (r1_tarski(k2_relat_1(sK5(X0,X1,X6)),X1) & k1_relat_1(sK5(X0,X1,X6)) = X0 & sK5(X0,X1,X6) = X6 & v1_funct_1(sK5(X0,X1,X6)) & v1_relat_1(sK5(X0,X1,X6))))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X1) & k1_relat_1(X5) = X0 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X1) | k1_relat_1(X7) != X0 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & (? [X8] : (r1_tarski(k2_relat_1(X8),X1) & k1_relat_1(X8) = X0 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) | ~r2_hidden(X6,X2))) | k1_funct_2(X0,X1) != X2))),
% 0.21/0.46    inference(rectify,[],[f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4))) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | ~r2_hidden(X3,X2))) | k1_funct_2(X0,X1) != X2))),
% 0.21/0.46    inference(nnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).
% 0.21/0.46  fof(f61,plain,(
% 0.21/0.46    sK0 = k1_relat_1(sK5(sK0,sK1,sK2))),
% 0.21/0.46    inference(resolution,[],[f38,f16])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    ( ! [X6,X0,X1] : (~r2_hidden(X6,k1_funct_2(X0,X1)) | k1_relat_1(sK5(X0,X1,X6)) = X0) )),
% 0.21/0.46    inference(equality_resolution,[],[f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ( ! [X6,X2,X0,X1] : (k1_relat_1(sK5(X0,X1,X6)) = X0 | ~r2_hidden(X6,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f121,plain,(
% 0.21/0.46    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))),
% 0.21/0.46    inference(subsumption_resolution,[],[f120,f104])).
% 0.21/0.46  fof(f104,plain,(
% 0.21/0.46    v1_relat_1(sK2)),
% 0.21/0.46    inference(superposition,[],[f57,f58])).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    v1_relat_1(sK5(sK0,sK1,sK2))),
% 0.21/0.46    inference(resolution,[],[f41,f16])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    ( ! [X6,X0,X1] : (~r2_hidden(X6,k1_funct_2(X0,X1)) | v1_relat_1(sK5(X0,X1,X6))) )),
% 0.21/0.46    inference(equality_resolution,[],[f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ( ! [X6,X2,X0,X1] : (v1_relat_1(sK5(X0,X1,X6)) | ~r2_hidden(X6,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f120,plain,(
% 0.21/0.46    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~v1_relat_1(sK2)),
% 0.21/0.46    inference(subsumption_resolution,[],[f63,f105])).
% 0.21/0.46  fof(f105,plain,(
% 0.21/0.46    v1_funct_1(sK2)),
% 0.21/0.46    inference(superposition,[],[f56,f58])).
% 0.21/0.46  fof(f56,plain,(
% 0.21/0.46    v1_funct_1(sK5(sK0,sK1,sK2))),
% 0.21/0.46    inference(resolution,[],[f40,f16])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    ( ! [X6,X0,X1] : (~r2_hidden(X6,k1_funct_2(X0,X1)) | v1_funct_1(sK5(X0,X1,X6))) )),
% 0.21/0.46    inference(equality_resolution,[],[f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ( ! [X6,X2,X0,X1] : (v1_funct_1(sK5(X0,X1,X6)) | ~r2_hidden(X6,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f63,plain,(
% 0.21/0.46    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.21/0.46    inference(resolution,[],[f60,f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,plain,(
% 0.21/0.46    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(flattening,[],[f6])).
% 0.21/0.46  fof(f6,plain,(
% 0.21/0.46    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 0.21/0.46  fof(f60,plain,(
% 0.21/0.46    r1_tarski(k2_relat_1(sK2),sK1)),
% 0.21/0.46    inference(forward_demodulation,[],[f59,f58])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    r1_tarski(k2_relat_1(sK5(sK0,sK1,sK2)),sK1)),
% 0.21/0.47    inference(resolution,[],[f37,f16])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X6,X0,X1] : (~r2_hidden(X6,k1_funct_2(X0,X1)) | r1_tarski(k2_relat_1(sK5(X0,X1,X6)),X1)) )),
% 0.21/0.47    inference(equality_resolution,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ( ! [X6,X2,X0,X1] : (r1_tarski(k2_relat_1(sK5(X0,X1,X6)),X1) | ~r2_hidden(X6,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f116,plain,(
% 0.21/0.47    spl6_2),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f115])).
% 0.21/0.47  fof(f115,plain,(
% 0.21/0.47    $false | spl6_2),
% 0.21/0.47    inference(subsumption_resolution,[],[f114,f49])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ~v1_funct_2(sK2,sK0,sK1) | spl6_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f47])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    spl6_2 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.47  fof(f114,plain,(
% 0.21/0.47    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.47    inference(forward_demodulation,[],[f113,f62])).
% 0.21/0.47  fof(f113,plain,(
% 0.21/0.47    v1_funct_2(sK2,k1_relat_1(sK2),sK1)),
% 0.21/0.47    inference(subsumption_resolution,[],[f112,f104])).
% 0.21/0.47  fof(f112,plain,(
% 0.21/0.47    v1_funct_2(sK2,k1_relat_1(sK2),sK1) | ~v1_relat_1(sK2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f65,f105])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    v1_funct_2(sK2,k1_relat_1(sK2),sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.21/0.47    inference(resolution,[],[f60,f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f107,plain,(
% 0.21/0.47    spl6_1),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f106])).
% 0.21/0.47  fof(f106,plain,(
% 0.21/0.47    $false | spl6_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f105,f45])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ~v1_funct_1(sK2) | spl6_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    spl6_1 <=> v1_funct_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ~spl6_1 | ~spl6_2 | ~spl6_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f17,f51,f47,f43])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (16694)------------------------------
% 0.21/0.47  % (16694)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (16694)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (16694)Memory used [KB]: 10618
% 0.21/0.47  % (16694)Time elapsed: 0.059 s
% 0.21/0.47  % (16694)------------------------------
% 0.21/0.47  % (16694)------------------------------
% 0.21/0.47  % (16682)Success in time 0.11 s
%------------------------------------------------------------------------------
