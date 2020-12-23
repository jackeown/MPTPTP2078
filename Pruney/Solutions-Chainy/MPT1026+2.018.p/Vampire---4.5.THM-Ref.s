%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:33 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  118 (11093 expanded)
%              Number of leaves         :   16 (3344 expanded)
%              Depth                    :   31
%              Number of atoms          :  383 (57157 expanded)
%              Number of equality atoms :  115 (11119 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f248,plain,(
    $false ),
    inference(subsumption_resolution,[],[f211,f247])).

fof(f247,plain,(
    ! [X0] : v1_funct_2(sK5,k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f246,f236])).

fof(f236,plain,(
    ! [X2,X3] : sP0(X2,sK5,X3) ),
    inference(resolution,[],[f205,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f20,f21])).

fof(f21,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f205,plain,(
    ! [X0,X1] : m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ),
    inference(subsumption_resolution,[],[f177,f204])).

fof(f204,plain,(
    ! [X0] : r1_tarski(sK3,X0) ),
    inference(subsumption_resolution,[],[f116,f201])).

fof(f201,plain,(
    ! [X5] : v4_relat_1(sK5,X5) ),
    inference(resolution,[],[f192,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | v4_relat_1(X1,X0) ) ),
    inference(superposition,[],[f58,f80])).

fof(f80,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f192,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f178,f80])).

fof(f178,plain,(
    ! [X0] : m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) ),
    inference(subsumption_resolution,[],[f171,f47])).

fof(f47,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f171,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) ) ),
    inference(backward_demodulation,[],[f138,f166])).

fof(f166,plain,(
    k1_xboole_0 = k2_relat_1(sK5) ),
    inference(forward_demodulation,[],[f165,f154])).

fof(f154,plain,(
    k1_xboole_0 = sK4 ),
    inference(subsumption_resolution,[],[f153,f141])).

fof(f141,plain,(
    ~ v1_funct_2(sK5,sK3,sK4) ),
    inference(subsumption_resolution,[],[f112,f140])).

fof(f140,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(resolution,[],[f138,f118])).

fof(f118,plain,(
    r1_tarski(k2_relat_1(sK5),sK4) ),
    inference(forward_demodulation,[],[f117,f105])).

fof(f105,plain,(
    sK5 = sK7(sK4,sK3,sK5) ),
    inference(resolution,[],[f104,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | sK7(X0,X1,X2) = X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ! [X3] :
            ( ~ r1_tarski(k2_relat_1(X3),X0)
            | k1_relat_1(X3) != X1
            | X2 != X3
            | ~ v1_funct_1(X3)
            | ~ v1_relat_1(X3) ) )
      & ( ( r1_tarski(k2_relat_1(sK7(X0,X1,X2)),X0)
          & k1_relat_1(sK7(X0,X1,X2)) = X1
          & sK7(X0,X1,X2) = X2
          & v1_funct_1(sK7(X0,X1,X2))
          & v1_relat_1(sK7(X0,X1,X2)) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f41,f42])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r1_tarski(k2_relat_1(X4),X0)
          & k1_relat_1(X4) = X1
          & X2 = X4
          & v1_funct_1(X4)
          & v1_relat_1(X4) )
     => ( r1_tarski(k2_relat_1(sK7(X0,X1,X2)),X0)
        & k1_relat_1(sK7(X0,X1,X2)) = X1
        & sK7(X0,X1,X2) = X2
        & v1_funct_1(sK7(X0,X1,X2))
        & v1_relat_1(sK7(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ! [X3] :
            ( ~ r1_tarski(k2_relat_1(X3),X0)
            | k1_relat_1(X3) != X1
            | X2 != X3
            | ~ v1_funct_1(X3)
            | ~ v1_relat_1(X3) ) )
      & ( ? [X4] :
            ( r1_tarski(k2_relat_1(X4),X0)
            & k1_relat_1(X4) = X1
            & X2 = X4
            & v1_funct_1(X4)
            & v1_relat_1(X4) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X1,X0,X3] :
      ( ( sP1(X1,X0,X3)
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
        | ~ sP1(X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X1,X0,X3] :
      ( sP1(X1,X0,X3)
    <=> ? [X4] :
          ( r1_tarski(k2_relat_1(X4),X1)
          & k1_relat_1(X4) = X0
          & X3 = X4
          & v1_funct_1(X4)
          & v1_relat_1(X4) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f104,plain,(
    sP1(sK4,sK3,sK5) ),
    inference(resolution,[],[f103,f89])).

fof(f89,plain,(
    ! [X0,X1] : sP2(X0,X1,k1_funct_2(X0,X1)) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ~ sP2(X0,X1,X2) )
      & ( sP2(X0,X1,X2)
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> sP2(X0,X1,X2) ) ),
    inference(definition_folding,[],[f9,f24,f23])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( sP2(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP1(X1,X0,X3) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f9,axiom,(
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

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ sP2(X1,X0,k1_funct_2(sK3,sK4))
      | sP1(X0,X1,sK5) ) ),
    inference(resolution,[],[f66,f45])).

fof(f45,plain,(
    r2_hidden(sK5,k1_funct_2(sK3,sK4)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      | ~ v1_funct_2(sK5,sK3,sK4)
      | ~ v1_funct_1(sK5) )
    & r2_hidden(sK5,k1_funct_2(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f13,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2) )
        & r2_hidden(X2,k1_funct_2(X0,X1)) )
   => ( ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
        | ~ v1_funct_2(sK5,sK3,sK4)
        | ~ v1_funct_1(sK5) )
      & r2_hidden(sK5,k1_funct_2(sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

fof(f66,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X2)
      | sP1(X1,X0,X4)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ( ~ sP1(X1,X0,sK6(X0,X1,X2))
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( sP1(X1,X0,sK6(X0,X1,X2))
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP1(X1,X0,X4) )
            & ( sP1(X1,X0,X4)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f37,f38])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP1(X1,X0,X3)
            | ~ r2_hidden(X3,X2) )
          & ( sP1(X1,X0,X3)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP1(X1,X0,sK6(X0,X1,X2))
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( sP1(X1,X0,sK6(X0,X1,X2))
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP1(X1,X0,X3)
              | ~ r2_hidden(X3,X2) )
            & ( sP1(X1,X0,X3)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP1(X1,X0,X4) )
            & ( sP1(X1,X0,X4)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP1(X1,X0,X3)
              | ~ r2_hidden(X3,X2) )
            & ( sP1(X1,X0,X3)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP1(X1,X0,X3) )
            & ( sP1(X1,X0,X3)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f117,plain,(
    r1_tarski(k2_relat_1(sK7(sK4,sK3,sK5)),sK4) ),
    inference(resolution,[],[f74,f104])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | r1_tarski(k2_relat_1(sK7(X0,X1,X2)),X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f112,plain,
    ( ~ v1_funct_2(sK5,sK3,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(subsumption_resolution,[],[f46,f111])).

fof(f111,plain,(
    v1_funct_1(sK5) ),
    inference(subsumption_resolution,[],[f110,f104])).

fof(f110,plain,
    ( v1_funct_1(sK5)
    | ~ sP1(sK4,sK3,sK5) ),
    inference(superposition,[],[f71,f105])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(sK7(X0,X1,X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f46,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_2(sK5,sK3,sK4)
    | ~ v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f27])).

fof(f153,plain,
    ( k1_xboole_0 = sK4
    | v1_funct_2(sK5,sK3,sK4) ),
    inference(subsumption_resolution,[],[f151,f145])).

fof(f145,plain,(
    sK3 = k1_relset_1(sK3,sK4,sK5) ),
    inference(forward_demodulation,[],[f142,f115])).

fof(f115,plain,(
    sK3 = k1_relat_1(sK5) ),
    inference(forward_demodulation,[],[f114,f105])).

fof(f114,plain,(
    sK3 = k1_relat_1(sK7(sK4,sK3,sK5)) ),
    inference(resolution,[],[f73,f104])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | k1_relat_1(sK7(X0,X1,X2)) = X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f142,plain,(
    k1_relat_1(sK5) = k1_relset_1(sK3,sK4,sK5) ),
    inference(resolution,[],[f140,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f151,plain,
    ( sK3 != k1_relset_1(sK3,sK4,sK5)
    | k1_xboole_0 = sK4
    | v1_funct_2(sK5,sK3,sK4) ),
    inference(resolution,[],[f61,f143])).

fof(f143,plain,(
    sP0(sK3,sK5,sK4) ),
    inference(resolution,[],[f140,f63])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | k1_relset_1(X0,X2,X1) != X0
      | k1_xboole_0 = X2
      | v1_funct_2(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f165,plain,(
    sK4 = k2_relat_1(sK5) ),
    inference(subsumption_resolution,[],[f160,f47])).

fof(f160,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK5))
    | sK4 = k2_relat_1(sK5) ),
    inference(backward_demodulation,[],[f119,f154])).

fof(f119,plain,
    ( ~ r1_tarski(sK4,k2_relat_1(sK5))
    | sK4 = k2_relat_1(sK5) ),
    inference(resolution,[],[f118,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f138,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK5),X0)
      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) ) ),
    inference(resolution,[],[f137,f78])).

fof(f78,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK3,X1)
      | ~ r1_tarski(k2_relat_1(sK5),X0)
      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(forward_demodulation,[],[f136,f115])).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(sK5),X0)
      | ~ r1_tarski(k1_relat_1(sK5),X1)
      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(resolution,[],[f56,f107])).

fof(f107,plain,(
    v1_relat_1(sK5) ),
    inference(forward_demodulation,[],[f106,f105])).

fof(f106,plain,(
    v1_relat_1(sK7(sK4,sK3,sK5)) ),
    inference(resolution,[],[f104,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | v1_relat_1(sK7(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f116,plain,(
    ! [X0] :
      ( ~ v4_relat_1(sK5,X0)
      | r1_tarski(sK3,X0) ) ),
    inference(backward_demodulation,[],[f109,f115])).

fof(f109,plain,(
    ! [X0] :
      ( ~ v4_relat_1(sK5,X0)
      | r1_tarski(k1_relat_1(sK5),X0) ) ),
    inference(resolution,[],[f107,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f177,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK3,X1)
      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(subsumption_resolution,[],[f170,f47])).

fof(f170,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | ~ r1_tarski(sK3,X1)
      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(backward_demodulation,[],[f137,f166])).

fof(f246,plain,(
    ! [X0] :
      ( v1_funct_2(sK5,k1_xboole_0,X0)
      | ~ sP0(k1_xboole_0,sK5,X0) ) ),
    inference(trivial_inequality_removal,[],[f245])).

fof(f245,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | v1_funct_2(sK5,k1_xboole_0,X0)
      | ~ sP0(k1_xboole_0,sK5,X0) ) ),
    inference(superposition,[],[f82,f240])).

fof(f240,plain,(
    ! [X0,X1] : k1_xboole_0 = k1_relset_1(X0,X1,sK5) ),
    inference(forward_demodulation,[],[f235,f208])).

fof(f208,plain,(
    k1_xboole_0 = k1_relat_1(sK5) ),
    inference(backward_demodulation,[],[f115,f207])).

fof(f207,plain,(
    k1_xboole_0 = sK3 ),
    inference(resolution,[],[f204,f92])).

fof(f92,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f52,f47])).

fof(f235,plain,(
    ! [X0,X1] : k1_relat_1(sK5) = k1_relset_1(X0,X1,sK5) ),
    inference(resolution,[],[f205,f57])).

fof(f82,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X2,X1)
      | v1_funct_2(X1,k1_xboole_0,X2)
      | ~ sP0(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X1,X0,X2)
      | k1_relset_1(X0,X2,X1) != X0
      | k1_xboole_0 != X0
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f211,plain,(
    ~ v1_funct_2(sK5,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f162,f207])).

fof(f162,plain,(
    ~ v1_funct_2(sK5,sK3,k1_xboole_0) ),
    inference(backward_demodulation,[],[f141,f154])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:03:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (22892)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.46  % (22900)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.50  % (22896)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (22915)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.51  % (22913)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.51  % (22905)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (22905)Refutation not found, incomplete strategy% (22905)------------------------------
% 0.22/0.52  % (22905)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (22905)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (22905)Memory used [KB]: 6268
% 0.22/0.52  % (22905)Time elapsed: 0.096 s
% 0.22/0.52  % (22905)------------------------------
% 0.22/0.52  % (22905)------------------------------
% 0.22/0.52  % (22903)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (22907)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.52  % (22899)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.52  % (22895)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.52  % (22909)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.53  % (22895)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f248,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(subsumption_resolution,[],[f211,f247])).
% 0.22/0.53  fof(f247,plain,(
% 0.22/0.53    ( ! [X0] : (v1_funct_2(sK5,k1_xboole_0,X0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f246,f236])).
% 0.22/0.53  fof(f236,plain,(
% 0.22/0.53    ( ! [X2,X3] : (sP0(X2,sK5,X3)) )),
% 0.22/0.53    inference(resolution,[],[f205,f63])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(nnf_transformation,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(definition_folding,[],[f20,f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 0.22/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(flattening,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.53  fof(f205,plain,(
% 0.22/0.53    ( ! [X0,X1] : (m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f177,f204])).
% 0.22/0.53  fof(f204,plain,(
% 0.22/0.53    ( ! [X0] : (r1_tarski(sK3,X0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f116,f201])).
% 0.22/0.53  fof(f201,plain,(
% 0.22/0.53    ( ! [X5] : (v4_relat_1(sK5,X5)) )),
% 0.22/0.53    inference(resolution,[],[f192,f96])).
% 0.22/0.53  fof(f96,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v4_relat_1(X1,X0)) )),
% 0.22/0.53    inference(superposition,[],[f58,f80])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f55])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.53    inference(flattening,[],[f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.53    inference(nnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.22/0.53    inference(pure_predicate_removal,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.53  fof(f192,plain,(
% 0.22/0.53    m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.53    inference(superposition,[],[f178,f80])).
% 0.22/0.53  fof(f178,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f171,f47])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.53  fof(f171,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))) )),
% 0.22/0.53    inference(backward_demodulation,[],[f138,f166])).
% 0.22/0.53  fof(f166,plain,(
% 0.22/0.53    k1_xboole_0 = k2_relat_1(sK5)),
% 0.22/0.53    inference(forward_demodulation,[],[f165,f154])).
% 0.22/0.53  fof(f154,plain,(
% 0.22/0.53    k1_xboole_0 = sK4),
% 0.22/0.53    inference(subsumption_resolution,[],[f153,f141])).
% 0.22/0.53  fof(f141,plain,(
% 0.22/0.53    ~v1_funct_2(sK5,sK3,sK4)),
% 0.22/0.53    inference(subsumption_resolution,[],[f112,f140])).
% 0.22/0.53  fof(f140,plain,(
% 0.22/0.53    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 0.22/0.53    inference(resolution,[],[f138,f118])).
% 0.22/0.53  fof(f118,plain,(
% 0.22/0.53    r1_tarski(k2_relat_1(sK5),sK4)),
% 0.22/0.53    inference(forward_demodulation,[],[f117,f105])).
% 0.22/0.53  fof(f105,plain,(
% 0.22/0.53    sK5 = sK7(sK4,sK3,sK5)),
% 0.22/0.53    inference(resolution,[],[f104,f72])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | sK7(X0,X1,X2) = X2) )),
% 0.22/0.53    inference(cnf_transformation,[],[f43])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ! [X3] : (~r1_tarski(k2_relat_1(X3),X0) | k1_relat_1(X3) != X1 | X2 != X3 | ~v1_funct_1(X3) | ~v1_relat_1(X3))) & ((r1_tarski(k2_relat_1(sK7(X0,X1,X2)),X0) & k1_relat_1(sK7(X0,X1,X2)) = X1 & sK7(X0,X1,X2) = X2 & v1_funct_1(sK7(X0,X1,X2)) & v1_relat_1(sK7(X0,X1,X2))) | ~sP1(X0,X1,X2)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f41,f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ! [X2,X1,X0] : (? [X4] : (r1_tarski(k2_relat_1(X4),X0) & k1_relat_1(X4) = X1 & X2 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) => (r1_tarski(k2_relat_1(sK7(X0,X1,X2)),X0) & k1_relat_1(sK7(X0,X1,X2)) = X1 & sK7(X0,X1,X2) = X2 & v1_funct_1(sK7(X0,X1,X2)) & v1_relat_1(sK7(X0,X1,X2))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ! [X3] : (~r1_tarski(k2_relat_1(X3),X0) | k1_relat_1(X3) != X1 | X2 != X3 | ~v1_funct_1(X3) | ~v1_relat_1(X3))) & (? [X4] : (r1_tarski(k2_relat_1(X4),X0) & k1_relat_1(X4) = X1 & X2 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | ~sP1(X0,X1,X2)))),
% 0.22/0.53    inference(rectify,[],[f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ! [X1,X0,X3] : ((sP1(X1,X0,X3) | ! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4))) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | ~sP1(X1,X0,X3)))),
% 0.22/0.53    inference(nnf_transformation,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X1,X0,X3] : (sP1(X1,X0,X3) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)))),
% 0.22/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.53  fof(f104,plain,(
% 0.22/0.53    sP1(sK4,sK3,sK5)),
% 0.22/0.53    inference(resolution,[],[f103,f89])).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    ( ! [X0,X1] : (sP2(X0,X1,k1_funct_2(X0,X1))) )),
% 0.22/0.53    inference(equality_resolution,[],[f76])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.22/0.53    inference(cnf_transformation,[],[f44])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ~sP2(X0,X1,X2)) & (sP2(X0,X1,X2) | k1_funct_2(X0,X1) != X2))),
% 0.22/0.53    inference(nnf_transformation,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> sP2(X0,X1,X2))),
% 0.22/0.53    inference(definition_folding,[],[f9,f24,f23])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (sP2(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP1(X1,X0,X3)))),
% 0.22/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).
% 0.22/0.53  fof(f103,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~sP2(X1,X0,k1_funct_2(sK3,sK4)) | sP1(X0,X1,sK5)) )),
% 0.22/0.53    inference(resolution,[],[f66,f45])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    r2_hidden(sK5,k1_funct_2(sK3,sK4))),
% 0.22/0.53    inference(cnf_transformation,[],[f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_2(sK5,sK3,sK4) | ~v1_funct_1(sK5)) & r2_hidden(sK5,k1_funct_2(sK3,sK4))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f13,f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1))) => ((~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_2(sK5,sK3,sK4) | ~v1_funct_1(sK5)) & r2_hidden(sK5,k1_funct_2(sK3,sK4)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.53    inference(negated_conjecture,[],[f10])).
% 0.22/0.53  fof(f10,conjecture,(
% 0.22/0.53    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X2) | sP1(X1,X0,X4) | ~sP2(X0,X1,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ((~sP1(X1,X0,sK6(X0,X1,X2)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sP1(X1,X0,sK6(X0,X1,X2)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP1(X1,X0,X4)) & (sP1(X1,X0,X4) | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f37,f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ! [X2,X1,X0] : (? [X3] : ((~sP1(X1,X0,X3) | ~r2_hidden(X3,X2)) & (sP1(X1,X0,X3) | r2_hidden(X3,X2))) => ((~sP1(X1,X0,sK6(X0,X1,X2)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sP1(X1,X0,sK6(X0,X1,X2)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : ((~sP1(X1,X0,X3) | ~r2_hidden(X3,X2)) & (sP1(X1,X0,X3) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP1(X1,X0,X4)) & (sP1(X1,X0,X4) | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 0.22/0.53    inference(rectify,[],[f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : ((~sP1(X1,X0,X3) | ~r2_hidden(X3,X2)) & (sP1(X1,X0,X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP1(X1,X0,X3)) & (sP1(X1,X0,X3) | ~r2_hidden(X3,X2))) | ~sP2(X0,X1,X2)))),
% 0.22/0.53    inference(nnf_transformation,[],[f24])).
% 0.22/0.53  fof(f117,plain,(
% 0.22/0.53    r1_tarski(k2_relat_1(sK7(sK4,sK3,sK5)),sK4)),
% 0.22/0.53    inference(resolution,[],[f74,f104])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | r1_tarski(k2_relat_1(sK7(X0,X1,X2)),X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f43])).
% 0.22/0.53  fof(f112,plain,(
% 0.22/0.53    ~v1_funct_2(sK5,sK3,sK4) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 0.22/0.53    inference(subsumption_resolution,[],[f46,f111])).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    v1_funct_1(sK5)),
% 0.22/0.53    inference(subsumption_resolution,[],[f110,f104])).
% 0.22/0.53  fof(f110,plain,(
% 0.22/0.53    v1_funct_1(sK5) | ~sP1(sK4,sK3,sK5)),
% 0.22/0.53    inference(superposition,[],[f71,f105])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (v1_funct_1(sK7(X0,X1,X2)) | ~sP1(X0,X1,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f43])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_2(sK5,sK3,sK4) | ~v1_funct_1(sK5)),
% 0.22/0.53    inference(cnf_transformation,[],[f27])).
% 0.22/0.53  fof(f153,plain,(
% 0.22/0.53    k1_xboole_0 = sK4 | v1_funct_2(sK5,sK3,sK4)),
% 0.22/0.53    inference(subsumption_resolution,[],[f151,f145])).
% 0.22/0.53  fof(f145,plain,(
% 0.22/0.53    sK3 = k1_relset_1(sK3,sK4,sK5)),
% 0.22/0.53    inference(forward_demodulation,[],[f142,f115])).
% 0.22/0.53  fof(f115,plain,(
% 0.22/0.53    sK3 = k1_relat_1(sK5)),
% 0.22/0.53    inference(forward_demodulation,[],[f114,f105])).
% 0.22/0.53  fof(f114,plain,(
% 0.22/0.53    sK3 = k1_relat_1(sK7(sK4,sK3,sK5))),
% 0.22/0.53    inference(resolution,[],[f73,f104])).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | k1_relat_1(sK7(X0,X1,X2)) = X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f43])).
% 0.22/0.53  fof(f142,plain,(
% 0.22/0.53    k1_relat_1(sK5) = k1_relset_1(sK3,sK4,sK5)),
% 0.22/0.53    inference(resolution,[],[f140,f57])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.53  fof(f151,plain,(
% 0.22/0.53    sK3 != k1_relset_1(sK3,sK4,sK5) | k1_xboole_0 = sK4 | v1_funct_2(sK5,sK3,sK4)),
% 0.22/0.53    inference(resolution,[],[f61,f143])).
% 0.22/0.53  fof(f143,plain,(
% 0.22/0.53    sP0(sK3,sK5,sK4)),
% 0.22/0.53    inference(resolution,[],[f140,f63])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | k1_relset_1(X0,X2,X1) != X0 | k1_xboole_0 = X2 | v1_funct_2(X1,X0,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 0.22/0.53    inference(rectify,[],[f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f21])).
% 0.22/0.53  fof(f165,plain,(
% 0.22/0.53    sK4 = k2_relat_1(sK5)),
% 0.22/0.53    inference(subsumption_resolution,[],[f160,f47])).
% 0.22/0.53  fof(f160,plain,(
% 0.22/0.53    ~r1_tarski(k1_xboole_0,k2_relat_1(sK5)) | sK4 = k2_relat_1(sK5)),
% 0.22/0.53    inference(backward_demodulation,[],[f119,f154])).
% 0.22/0.53  fof(f119,plain,(
% 0.22/0.53    ~r1_tarski(sK4,k2_relat_1(sK5)) | sK4 = k2_relat_1(sK5)),
% 0.22/0.53    inference(resolution,[],[f118,f52])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.53    inference(flattening,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.53  fof(f138,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_tarski(k2_relat_1(sK5),X0) | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))) )),
% 0.22/0.53    inference(resolution,[],[f137,f78])).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.53    inference(equality_resolution,[],[f51])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f30])).
% 0.22/0.53  fof(f137,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(sK3,X1) | ~r1_tarski(k2_relat_1(sK5),X0) | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.22/0.53    inference(forward_demodulation,[],[f136,f115])).
% 0.22/0.53  fof(f136,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK5),X0) | ~r1_tarski(k1_relat_1(sK5),X1) | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.22/0.53    inference(resolution,[],[f56,f107])).
% 0.22/0.53  fof(f107,plain,(
% 0.22/0.53    v1_relat_1(sK5)),
% 0.22/0.53    inference(forward_demodulation,[],[f106,f105])).
% 0.22/0.53  fof(f106,plain,(
% 0.22/0.53    v1_relat_1(sK7(sK4,sK3,sK5))),
% 0.22/0.53    inference(resolution,[],[f104,f70])).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | v1_relat_1(sK7(X0,X1,X2))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f43])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.22/0.53    inference(flattening,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 0.22/0.53  fof(f116,plain,(
% 0.22/0.53    ( ! [X0] : (~v4_relat_1(sK5,X0) | r1_tarski(sK3,X0)) )),
% 0.22/0.53    inference(backward_demodulation,[],[f109,f115])).
% 0.22/0.53  fof(f109,plain,(
% 0.22/0.53    ( ! [X0] : (~v4_relat_1(sK5,X0) | r1_tarski(k1_relat_1(sK5),X0)) )),
% 0.22/0.53    inference(resolution,[],[f107,f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.22/0.53  fof(f177,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(sK3,X1) | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f170,f47])).
% 0.22/0.53  fof(f170,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,X0) | ~r1_tarski(sK3,X1) | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.22/0.53    inference(backward_demodulation,[],[f137,f166])).
% 0.22/0.53  fof(f246,plain,(
% 0.22/0.53    ( ! [X0] : (v1_funct_2(sK5,k1_xboole_0,X0) | ~sP0(k1_xboole_0,sK5,X0)) )),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f245])).
% 0.22/0.53  fof(f245,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | v1_funct_2(sK5,k1_xboole_0,X0) | ~sP0(k1_xboole_0,sK5,X0)) )),
% 0.22/0.53    inference(superposition,[],[f82,f240])).
% 0.22/0.53  fof(f240,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_xboole_0 = k1_relset_1(X0,X1,sK5)) )),
% 0.22/0.53    inference(forward_demodulation,[],[f235,f208])).
% 0.22/0.53  fof(f208,plain,(
% 0.22/0.53    k1_xboole_0 = k1_relat_1(sK5)),
% 0.22/0.53    inference(backward_demodulation,[],[f115,f207])).
% 0.22/0.53  fof(f207,plain,(
% 0.22/0.53    k1_xboole_0 = sK3),
% 0.22/0.53    inference(resolution,[],[f204,f92])).
% 0.22/0.53  fof(f92,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.22/0.53    inference(resolution,[],[f52,f47])).
% 0.22/0.53  fof(f235,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_relat_1(sK5) = k1_relset_1(X0,X1,sK5)) )),
% 0.22/0.53    inference(resolution,[],[f205,f57])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X2,X1) | v1_funct_2(X1,k1_xboole_0,X2) | ~sP0(k1_xboole_0,X1,X2)) )),
% 0.22/0.53    inference(equality_resolution,[],[f62])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0 | k1_xboole_0 != X0 | ~sP0(X0,X1,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f211,plain,(
% 0.22/0.53    ~v1_funct_2(sK5,k1_xboole_0,k1_xboole_0)),
% 0.22/0.53    inference(backward_demodulation,[],[f162,f207])).
% 0.22/0.53  fof(f162,plain,(
% 0.22/0.53    ~v1_funct_2(sK5,sK3,k1_xboole_0)),
% 0.22/0.53    inference(backward_demodulation,[],[f141,f154])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (22895)------------------------------
% 0.22/0.53  % (22895)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (22895)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (22895)Memory used [KB]: 6268
% 0.22/0.53  % (22895)Time elapsed: 0.105 s
% 0.22/0.53  % (22895)------------------------------
% 0.22/0.53  % (22895)------------------------------
% 0.22/0.53  % (22891)Success in time 0.166 s
%------------------------------------------------------------------------------
