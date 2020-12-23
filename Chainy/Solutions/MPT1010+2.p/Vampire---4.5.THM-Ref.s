%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1010+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:02 EST 2020

% Result     : Theorem 2.74s
% Output     : Refutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :   55 (  88 expanded)
%              Number of leaves         :   13 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :  196 ( 354 expanded)
%              Number of equality atoms :   56 (  88 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4534,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3335,f3340,f3350,f3360,f3380,f4375,f4512])).

fof(f4512,plain,
    ( ~ spl197_1
    | ~ spl197_2
    | ~ spl197_4
    | spl197_6
    | ~ spl197_10
    | spl197_38 ),
    inference(avatar_contradiction_clause,[],[f4511])).

fof(f4511,plain,
    ( $false
    | ~ spl197_1
    | ~ spl197_2
    | ~ spl197_4
    | spl197_6
    | ~ spl197_10
    | spl197_38 ),
    inference(subsumption_resolution,[],[f4494,f3130])).

fof(f3130,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k1_tarski(X1)) ),
    inference(equality_resolution,[],[f2567])).

fof(f2567,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f2143])).

fof(f2143,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f2142])).

fof(f2142,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f397])).

fof(f397,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

fof(f4494,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(sK5,sK4)))
    | ~ spl197_1
    | ~ spl197_2
    | ~ spl197_4
    | spl197_6
    | ~ spl197_10
    | spl197_38 ),
    inference(backward_demodulation,[],[f3506,f4488])).

fof(f4488,plain,
    ( k1_xboole_0 = k1_tarski(sK3)
    | ~ spl197_1
    | ~ spl197_2
    | ~ spl197_4
    | ~ spl197_10
    | spl197_38 ),
    inference(unit_resulting_resolution,[],[f3334,f3339,f3349,f3379,f4374,f2528])).

fof(f2528,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X3,X0,X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(k1_funct_1(X3,X2),X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f1655])).

fof(f1655,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f1654])).

fof(f1654,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f1544])).

fof(f1544,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

fof(f4374,plain,
    ( ~ r2_hidden(k1_funct_1(sK5,sK4),k1_tarski(sK3))
    | spl197_38 ),
    inference(avatar_component_clause,[],[f4372])).

fof(f4372,plain,
    ( spl197_38
  <=> r2_hidden(k1_funct_1(sK5,sK4),k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl197_38])])).

fof(f3379,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
    | ~ spl197_10 ),
    inference(avatar_component_clause,[],[f3377])).

fof(f3377,plain,
    ( spl197_10
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl197_10])])).

fof(f3349,plain,
    ( v1_funct_2(sK5,sK2,k1_tarski(sK3))
    | ~ spl197_4 ),
    inference(avatar_component_clause,[],[f3347])).

fof(f3347,plain,
    ( spl197_4
  <=> v1_funct_2(sK5,sK2,k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl197_4])])).

fof(f3339,plain,
    ( r2_hidden(sK4,sK2)
    | ~ spl197_2 ),
    inference(avatar_component_clause,[],[f3337])).

fof(f3337,plain,
    ( spl197_2
  <=> r2_hidden(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl197_2])])).

fof(f3334,plain,
    ( v1_funct_1(sK5)
    | ~ spl197_1 ),
    inference(avatar_component_clause,[],[f3332])).

fof(f3332,plain,
    ( spl197_1
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl197_1])])).

fof(f3506,plain,
    ( ~ r1_tarski(k1_tarski(sK3),k1_tarski(k1_funct_1(sK5,sK4)))
    | spl197_6 ),
    inference(unit_resulting_resolution,[],[f3359,f2576])).

fof(f2576,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1670])).

fof(f1670,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f381])).

fof(f381,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_zfmisc_1)).

fof(f3359,plain,
    ( sK3 != k1_funct_1(sK5,sK4)
    | spl197_6 ),
    inference(avatar_component_clause,[],[f3357])).

fof(f3357,plain,
    ( spl197_6
  <=> sK3 = k1_funct_1(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl197_6])])).

fof(f4375,plain,
    ( ~ spl197_38
    | spl197_6 ),
    inference(avatar_split_clause,[],[f3465,f3357,f4372])).

fof(f3465,plain,
    ( ~ r2_hidden(k1_funct_1(sK5,sK4),k1_tarski(sK3))
    | spl197_6 ),
    inference(unit_resulting_resolution,[],[f3359,f3135])).

fof(f3135,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f2572])).

fof(f2572,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2149])).

fof(f2149,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK50(X0,X1) != X0
            | ~ r2_hidden(sK50(X0,X1),X1) )
          & ( sK50(X0,X1) = X0
            | r2_hidden(sK50(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK50])],[f2147,f2148])).

fof(f2148,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK50(X0,X1) != X0
          | ~ r2_hidden(sK50(X0,X1),X1) )
        & ( sK50(X0,X1) = X0
          | r2_hidden(sK50(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f2147,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f2146])).

fof(f2146,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f175])).

fof(f175,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f3380,plain,(
    spl197_10 ),
    inference(avatar_split_clause,[],[f2350,f3377])).

fof(f2350,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) ),
    inference(cnf_transformation,[],[f2040])).

fof(f2040,plain,
    ( sK3 != k1_funct_1(sK5,sK4)
    & r2_hidden(sK4,sK2)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
    & v1_funct_2(sK5,sK2,k1_tarski(sK3))
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f1558,f2039])).

fof(f2039,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( sK3 != k1_funct_1(sK5,sK4)
      & r2_hidden(sK4,sK2)
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
      & v1_funct_2(sK5,sK2,k1_tarski(sK3))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f1558,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f1557])).

fof(f1557,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f1542])).

fof(f1542,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f1541])).

fof(f1541,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

fof(f3360,plain,(
    ~ spl197_6 ),
    inference(avatar_split_clause,[],[f2352,f3357])).

fof(f2352,plain,(
    sK3 != k1_funct_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f2040])).

fof(f3350,plain,(
    spl197_4 ),
    inference(avatar_split_clause,[],[f2349,f3347])).

fof(f2349,plain,(
    v1_funct_2(sK5,sK2,k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f2040])).

fof(f3340,plain,(
    spl197_2 ),
    inference(avatar_split_clause,[],[f2351,f3337])).

fof(f2351,plain,(
    r2_hidden(sK4,sK2) ),
    inference(cnf_transformation,[],[f2040])).

fof(f3335,plain,(
    spl197_1 ),
    inference(avatar_split_clause,[],[f2348,f3332])).

fof(f2348,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f2040])).
%------------------------------------------------------------------------------
