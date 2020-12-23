%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 398 expanded)
%              Number of leaves         :   26 ( 138 expanded)
%              Depth                    :   16
%              Number of atoms          :  511 (2271 expanded)
%              Number of equality atoms :   86 ( 159 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f494,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f280,f405,f423,f433,f477,f486,f493])).

fof(f493,plain,(
    ~ spl9_11 ),
    inference(avatar_contradiction_clause,[],[f492])).

fof(f492,plain,
    ( $false
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f491,f56])).

fof(f56,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f491,plain,
    ( ~ r1_tarski(k1_xboole_0,sK4)
    | ~ spl9_11 ),
    inference(forward_demodulation,[],[f490,f178])).

fof(f178,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f171,f98])).

fof(f98,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f60,f56])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
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

fof(f171,plain,(
    ! [X3] : r1_tarski(k2_relat_1(k1_xboole_0),X3) ),
    inference(resolution,[],[f164,f56])).

fof(f164,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | r1_tarski(k2_relat_1(X0),X2) ) ),
    inference(resolution,[],[f143,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f143,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(k2_relat_1(X3),k1_zfmisc_1(X4))
      | ~ r1_tarski(X3,k2_zfmisc_1(X5,X4)) ) ),
    inference(resolution,[],[f140,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1)) ) ),
    inference(duplicate_literal_removal,[],[f139])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f66,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f490,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),sK4)
    | ~ spl9_11 ),
    inference(backward_demodulation,[],[f134,f472])).

fof(f472,plain,
    ( k1_xboole_0 = sK7
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f470])).

fof(f470,plain,
    ( spl9_11
  <=> k1_xboole_0 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f134,plain,(
    ~ r1_tarski(k2_relat_1(sK7),sK4) ),
    inference(subsumption_resolution,[],[f133,f53])).

fof(f53,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),sK4)
    & ! [X4] :
        ( r2_hidden(k3_funct_2(sK5,sK6,sK7,X4),sK4)
        | ~ m1_subset_1(X4,sK5) )
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_2(sK7,sK5,sK6)
    & v1_funct_1(sK7)
    & ~ v1_xboole_0(sK6)
    & ~ v1_xboole_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f15,f35,f34,f33])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
                & ! [X4] :
                    ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                    | ~ m1_subset_1(X4,X1) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(X3,X1,X2)
                & v1_funct_1(X3) )
            & ~ v1_xboole_0(X2) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(sK5,X2,X3),sK4)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(sK5,X2,X3,X4),sK4)
                  | ~ m1_subset_1(X4,sK5) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X2)))
              & v1_funct_2(X3,sK5,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k2_relset_1(sK5,X2,X3),sK4)
            & ! [X4] :
                ( r2_hidden(k3_funct_2(sK5,X2,X3,X4),sK4)
                | ~ m1_subset_1(X4,sK5) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X2)))
            & v1_funct_2(X3,sK5,X2)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k2_relset_1(sK5,sK6,X3),sK4)
          & ! [X4] :
              ( r2_hidden(k3_funct_2(sK5,sK6,X3,X4),sK4)
              | ~ m1_subset_1(X4,sK5) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
          & v1_funct_2(X3,sK5,sK6)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k2_relset_1(sK5,sK6,X3),sK4)
        & ! [X4] :
            ( r2_hidden(k3_funct_2(sK5,sK6,X3,X4),sK4)
            | ~ m1_subset_1(X4,sK5) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
        & v1_funct_2(X3,sK5,sK6)
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),sK4)
      & ! [X4] :
          ( r2_hidden(k3_funct_2(sK5,sK6,sK7,X4),sK4)
          | ~ m1_subset_1(X4,sK5) )
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      & v1_funct_2(sK7,sK5,sK6)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                  | ~ m1_subset_1(X4,X1) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                  | ~ m1_subset_1(X4,X1) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_2(X3,X1,X2)
                  & v1_funct_1(X3) )
               => ( ! [X4] :
                      ( m1_subset_1(X4,X1)
                     => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) )
                 => r1_tarski(k2_relset_1(X1,X2,X3),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(X3,X1,X2)
                & v1_funct_1(X3) )
             => ( ! [X4] :
                    ( m1_subset_1(X4,X1)
                   => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) )
               => r1_tarski(k2_relset_1(X1,X2,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t191_funct_2)).

fof(f133,plain,
    ( ~ r1_tarski(k2_relat_1(sK7),sK4)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(superposition,[],[f55,f65])).

fof(f55,plain,(
    ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f486,plain,
    ( ~ spl9_10
    | ~ spl9_12 ),
    inference(avatar_contradiction_clause,[],[f485])).

fof(f485,plain,
    ( $false
    | ~ spl9_10
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f484,f86])).

fof(f86,plain,(
    ! [X1] : ~ sP0(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f484,plain,
    ( sP0(k1_xboole_0,k1_xboole_0)
    | ~ spl9_10
    | ~ spl9_12 ),
    inference(backward_demodulation,[],[f449,f476])).

fof(f476,plain,
    ( k1_xboole_0 = sK5
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f474])).

fof(f474,plain,
    ( spl9_12
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f449,plain,
    ( sP0(sK5,k1_xboole_0)
    | ~ spl9_10 ),
    inference(backward_demodulation,[],[f404,f434])).

fof(f434,plain,
    ( k1_xboole_0 = sK6
    | ~ spl9_10 ),
    inference(resolution,[],[f404,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f404,plain,
    ( sP0(sK5,sK6)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f402])).

fof(f402,plain,
    ( spl9_10
  <=> sP0(sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f477,plain,
    ( spl9_11
    | spl9_12
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f468,f402,f474,f470])).

fof(f468,plain,
    ( k1_xboole_0 = sK5
    | k1_xboole_0 = sK7
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f467,f436])).

fof(f436,plain,
    ( v1_funct_2(sK7,sK5,k1_xboole_0)
    | ~ spl9_10 ),
    inference(backward_demodulation,[],[f52,f434])).

fof(f52,plain,(
    v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f36])).

fof(f467,plain,
    ( ~ v1_funct_2(sK7,sK5,k1_xboole_0)
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK7
    | ~ spl9_10 ),
    inference(resolution,[],[f443,f85])).

fof(f85,plain,(
    ! [X2,X0] :
      ( ~ sP2(X0,k1_xboole_0,X2)
      | ~ v1_funct_2(X0,X2,k1_xboole_0)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ v1_funct_2(X0,X2,X1)
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X0,X2,X1)
          | k1_xboole_0 != X0 )
        & ( k1_xboole_0 = X0
          | ~ v1_funct_2(X0,X2,X1) ) )
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_xboole_0 != X2 )
        & ( k1_xboole_0 = X2
          | ~ v1_funct_2(X2,X0,X1) ) )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP2(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP2(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f443,plain,
    ( sP2(sK7,k1_xboole_0,sK5)
    | ~ spl9_10 ),
    inference(backward_demodulation,[],[f115,f434])).

fof(f115,plain,(
    sP2(sK7,sK6,sK5) ),
    inference(resolution,[],[f74,f53])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP2(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X2,X1,X0)
        & sP1(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f22,f29,f28,f27])).

fof(f28,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f433,plain,
    ( ~ spl9_7
    | ~ spl9_9 ),
    inference(avatar_contradiction_clause,[],[f432])).

fof(f432,plain,
    ( $false
    | ~ spl9_7
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f426,f134])).

fof(f426,plain,
    ( r1_tarski(k2_relat_1(sK7),sK4)
    | ~ spl9_7
    | ~ spl9_9 ),
    inference(resolution,[],[f425,f157])).

fof(f157,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | r1_tarski(k2_relat_1(X2),X0) ) ),
    inference(resolution,[],[f142,f61])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(X1))
      | ~ sP3(X1,X2,X0) ) ),
    inference(resolution,[],[f140,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(X2,X1,X0)
        & v1_funct_1(X2) )
      | ~ sP3(X0,X1,X2) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X1,X0,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ sP3(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X1,X0,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ sP3(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f425,plain,
    ( sP3(sK4,sK5,sK7)
    | ~ spl9_7
    | ~ spl9_9 ),
    inference(forward_demodulation,[],[f275,f400])).

fof(f400,plain,
    ( sK5 = k1_relat_1(sK7)
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f398])).

fof(f398,plain,
    ( spl9_9
  <=> sK5 = k1_relat_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f275,plain,
    ( sP3(sK4,k1_relat_1(sK7),sK7)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl9_7
  <=> sP3(sK4,k1_relat_1(sK7),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f423,plain,
    ( spl9_8
    | ~ spl9_9 ),
    inference(avatar_contradiction_clause,[],[f422])).

fof(f422,plain,
    ( $false
    | spl9_8
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f416,f134])).

fof(f416,plain,
    ( r1_tarski(k2_relat_1(sK7),sK4)
    | spl9_8
    | ~ spl9_9 ),
    inference(resolution,[],[f415,f157])).

fof(f415,plain,
    ( sP3(sK4,sK5,sK7)
    | spl9_8
    | ~ spl9_9 ),
    inference(resolution,[],[f413,f406])).

fof(f406,plain,
    ( ~ r2_hidden(sK8(sK5,sK4,sK7),sK5)
    | spl9_8
    | ~ spl9_9 ),
    inference(backward_demodulation,[],[f281,f400])).

fof(f281,plain,
    ( ~ r2_hidden(sK8(k1_relat_1(sK7),sK4,sK7),sK5)
    | spl9_8 ),
    inference(resolution,[],[f279,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f279,plain,
    ( ~ m1_subset_1(sK8(k1_relat_1(sK7),sK4,sK7),sK5)
    | spl9_8 ),
    inference(avatar_component_clause,[],[f277])).

fof(f277,plain,
    ( spl9_8
  <=> m1_subset_1(sK8(k1_relat_1(sK7),sK4,sK7),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f413,plain,
    ( ! [X1] :
        ( r2_hidden(sK8(sK5,X1,sK7),sK5)
        | sP3(X1,sK5,sK7) )
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f412,f92])).

fof(f92,plain,(
    v1_relat_1(sK7) ),
    inference(resolution,[],[f63,f53])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f412,plain,
    ( ! [X1] :
        ( r2_hidden(sK8(sK5,X1,sK7),sK5)
        | sP3(X1,sK5,sK7)
        | ~ v1_relat_1(sK7) )
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f409,f51])).

fof(f51,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f36])).

fof(f409,plain,
    ( ! [X1] :
        ( r2_hidden(sK8(sK5,X1,sK7),sK5)
        | sP3(X1,sK5,sK7)
        | ~ v1_funct_1(sK7)
        | ~ v1_relat_1(sK7) )
    | ~ spl9_9 ),
    inference(superposition,[],[f88,f400])).

fof(f88,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK8(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | sP3(X1,k1_relat_1(X2),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( sP3(X1,X0,X2)
      | r2_hidden(sK8(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( sP3(X1,X0,X2)
      | ( ~ r2_hidden(k1_funct_1(X2,sK8(X0,X1,X2)),X1)
        & r2_hidden(sK8(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f32,f47])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK8(X0,X1,X2)),X1)
        & r2_hidden(sK8(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( sP3(X1,X0,X2)
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_folding,[],[f24,f31])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f405,plain,
    ( spl9_9
    | spl9_10 ),
    inference(avatar_split_clause,[],[f396,f402,f398])).

fof(f396,plain,
    ( sP0(sK5,sK6)
    | sK5 = k1_relat_1(sK7) ),
    inference(subsumption_resolution,[],[f394,f52])).

fof(f394,plain,
    ( ~ v1_funct_2(sK7,sK5,sK6)
    | sP0(sK5,sK6)
    | sK5 = k1_relat_1(sK7) ),
    inference(resolution,[],[f186,f53])).

fof(f186,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X5,X3,X4)
      | sP0(X3,X4)
      | k1_relat_1(X5) = X3 ) ),
    inference(subsumption_resolution,[],[f184,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f184,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | sP0(X3,X4)
      | ~ sP1(X3,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f69,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f280,plain,
    ( spl9_7
    | ~ spl9_8 ),
    inference(avatar_split_clause,[],[f271,f277,f273])).

fof(f271,plain,
    ( ~ m1_subset_1(sK8(k1_relat_1(sK7),sK4,sK7),sK5)
    | sP3(sK4,k1_relat_1(sK7),sK7) ),
    inference(subsumption_resolution,[],[f270,f92])).

fof(f270,plain,
    ( ~ m1_subset_1(sK8(k1_relat_1(sK7),sK4,sK7),sK5)
    | sP3(sK4,k1_relat_1(sK7),sK7)
    | ~ v1_relat_1(sK7) ),
    inference(subsumption_resolution,[],[f269,f51])).

fof(f269,plain,
    ( ~ m1_subset_1(sK8(k1_relat_1(sK7),sK4,sK7),sK5)
    | sP3(sK4,k1_relat_1(sK7),sK7)
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7) ),
    inference(resolution,[],[f268,f87])).

fof(f87,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(k1_funct_1(X2,sK8(k1_relat_1(X2),X1,X2)),X1)
      | sP3(X1,k1_relat_1(X2),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( sP3(X1,X0,X2)
      | ~ r2_hidden(k1_funct_1(X2,sK8(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f268,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK7,X0),sK4)
      | ~ m1_subset_1(X0,sK5) ) ),
    inference(subsumption_resolution,[],[f267,f49])).

fof(f49,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f267,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK7,X0),sK4)
      | ~ m1_subset_1(X0,sK5)
      | v1_xboole_0(sK5) ) ),
    inference(subsumption_resolution,[],[f266,f51])).

fof(f266,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK7,X0),sK4)
      | ~ m1_subset_1(X0,sK5)
      | ~ v1_funct_1(sK7)
      | v1_xboole_0(sK5) ) ),
    inference(subsumption_resolution,[],[f265,f52])).

fof(f265,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK7,X0),sK4)
      | ~ m1_subset_1(X0,sK5)
      | ~ v1_funct_2(sK7,sK5,sK6)
      | ~ v1_funct_1(sK7)
      | v1_xboole_0(sK5) ) ),
    inference(subsumption_resolution,[],[f264,f53])).

fof(f264,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK7,X0),sK4)
      | ~ m1_subset_1(X0,sK5)
      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      | ~ v1_funct_2(sK7,sK5,sK6)
      | ~ v1_funct_1(sK7)
      | v1_xboole_0(sK5) ) ),
    inference(duplicate_literal_removal,[],[f263])).

fof(f263,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK7,X0),sK4)
      | ~ m1_subset_1(X0,sK5)
      | ~ m1_subset_1(X0,sK5)
      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      | ~ v1_funct_2(sK7,sK5,sK6)
      | ~ v1_funct_1(sK7)
      | v1_xboole_0(sK5) ) ),
    inference(superposition,[],[f54,f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f54,plain,(
    ! [X4] :
      ( r2_hidden(k3_funct_2(sK5,sK6,sK7,X4),sK4)
      | ~ m1_subset_1(X4,sK5) ) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:14:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.54  % (7432)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.54  % (7447)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.54  % (7441)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.54  % (7435)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.54  % (7440)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.54  % (7431)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.54  % (7444)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.54  % (7443)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.54  % (7427)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.55  % (7428)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.55  % (7448)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.55  % (7429)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.55  % (7433)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.55  % (7428)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % (7436)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.55  % (7439)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.55  % (7442)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.56  % (7434)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.56  % (7437)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.56  % (7438)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.56  % (7426)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.56  % (7430)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.57  % (7424)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.57  % (7435)Refutation not found, incomplete strategy% (7435)------------------------------
% 0.21/0.57  % (7435)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (7449)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.57  % (7435)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (7435)Memory used [KB]: 10746
% 0.21/0.57  % (7435)Time elapsed: 0.133 s
% 0.21/0.57  % (7435)------------------------------
% 0.21/0.57  % (7435)------------------------------
% 0.21/0.57  % (7425)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f494,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(avatar_sat_refutation,[],[f280,f405,f423,f433,f477,f486,f493])).
% 0.21/0.57  fof(f493,plain,(
% 0.21/0.57    ~spl9_11),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f492])).
% 0.21/0.57  fof(f492,plain,(
% 0.21/0.57    $false | ~spl9_11),
% 0.21/0.57    inference(subsumption_resolution,[],[f491,f56])).
% 0.21/0.57  fof(f56,plain,(
% 0.21/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.57  fof(f491,plain,(
% 0.21/0.57    ~r1_tarski(k1_xboole_0,sK4) | ~spl9_11),
% 0.21/0.57    inference(forward_demodulation,[],[f490,f178])).
% 0.21/0.57  fof(f178,plain,(
% 0.21/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.57    inference(resolution,[],[f171,f98])).
% 0.21/0.57  fof(f98,plain,(
% 0.21/0.57    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.57    inference(resolution,[],[f60,f56])).
% 0.21/0.57  fof(f60,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f38])).
% 0.21/0.57  fof(f38,plain,(
% 0.21/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.57    inference(flattening,[],[f37])).
% 0.21/0.57  fof(f37,plain,(
% 0.21/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.57    inference(nnf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.57  fof(f171,plain,(
% 0.21/0.57    ( ! [X3] : (r1_tarski(k2_relat_1(k1_xboole_0),X3)) )),
% 0.21/0.57    inference(resolution,[],[f164,f56])).
% 0.21/0.57  fof(f164,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | r1_tarski(k2_relat_1(X0),X2)) )),
% 0.21/0.57    inference(resolution,[],[f143,f61])).
% 0.21/0.57  fof(f61,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f39])).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.57    inference(nnf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.57  fof(f143,plain,(
% 0.21/0.57    ( ! [X4,X5,X3] : (m1_subset_1(k2_relat_1(X3),k1_zfmisc_1(X4)) | ~r1_tarski(X3,k2_zfmisc_1(X5,X4))) )),
% 0.21/0.57    inference(resolution,[],[f140,f62])).
% 0.21/0.57  fof(f62,plain,(
% 0.21/0.57    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f39])).
% 0.21/0.57  fof(f140,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1))) )),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f139])).
% 0.21/0.57  fof(f139,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.57    inference(superposition,[],[f66,f65])).
% 0.21/0.57  fof(f65,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f19])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(ennf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.57  fof(f66,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f20])).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(ennf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.21/0.57  fof(f490,plain,(
% 0.21/0.57    ~r1_tarski(k2_relat_1(k1_xboole_0),sK4) | ~spl9_11),
% 0.21/0.57    inference(backward_demodulation,[],[f134,f472])).
% 0.21/0.57  fof(f472,plain,(
% 0.21/0.57    k1_xboole_0 = sK7 | ~spl9_11),
% 0.21/0.57    inference(avatar_component_clause,[],[f470])).
% 0.21/0.57  fof(f470,plain,(
% 0.21/0.57    spl9_11 <=> k1_xboole_0 = sK7),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 0.21/0.57  fof(f134,plain,(
% 0.21/0.57    ~r1_tarski(k2_relat_1(sK7),sK4)),
% 0.21/0.57    inference(subsumption_resolution,[],[f133,f53])).
% 0.21/0.57  fof(f53,plain,(
% 0.21/0.57    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 0.21/0.57    inference(cnf_transformation,[],[f36])).
% 0.21/0.57  fof(f36,plain,(
% 0.21/0.57    ((~r1_tarski(k2_relset_1(sK5,sK6,sK7),sK4) & ! [X4] : (r2_hidden(k3_funct_2(sK5,sK6,sK7,X4),sK4) | ~m1_subset_1(X4,sK5)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7)) & ~v1_xboole_0(sK6)) & ~v1_xboole_0(sK5)),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f15,f35,f34,f33])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(sK5,X2,X3),sK4) & ! [X4] : (r2_hidden(k3_funct_2(sK5,X2,X3,X4),sK4) | ~m1_subset_1(X4,sK5)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X2))) & v1_funct_2(X3,sK5,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK5))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    ? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(sK5,X2,X3),sK4) & ! [X4] : (r2_hidden(k3_funct_2(sK5,X2,X3,X4),sK4) | ~m1_subset_1(X4,sK5)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X2))) & v1_funct_2(X3,sK5,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (~r1_tarski(k2_relset_1(sK5,sK6,X3),sK4) & ! [X4] : (r2_hidden(k3_funct_2(sK5,sK6,X3,X4),sK4) | ~m1_subset_1(X4,sK5)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(X3,sK5,sK6) & v1_funct_1(X3)) & ~v1_xboole_0(sK6))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    ? [X3] : (~r1_tarski(k2_relset_1(sK5,sK6,X3),sK4) & ! [X4] : (r2_hidden(k3_funct_2(sK5,sK6,X3,X4),sK4) | ~m1_subset_1(X4,sK5)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(X3,sK5,sK6) & v1_funct_1(X3)) => (~r1_tarski(k2_relset_1(sK5,sK6,sK7),sK4) & ! [X4] : (r2_hidden(k3_funct_2(sK5,sK6,sK7,X4),sK4) | ~m1_subset_1(X4,sK5)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f15,plain,(
% 0.21/0.57    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 0.21/0.57    inference(flattening,[],[f14])).
% 0.21/0.57  fof(f14,plain,(
% 0.21/0.57    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f13])).
% 0.21/0.57  fof(f13,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 0.21/0.57    inference(negated_conjecture,[],[f12])).
% 0.21/0.57  fof(f12,conjecture,(
% 0.21/0.57    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t191_funct_2)).
% 0.21/0.57  fof(f133,plain,(
% 0.21/0.57    ~r1_tarski(k2_relat_1(sK7),sK4) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 0.21/0.57    inference(superposition,[],[f55,f65])).
% 0.21/0.57  fof(f55,plain,(
% 0.21/0.57    ~r1_tarski(k2_relset_1(sK5,sK6,sK7),sK4)),
% 0.21/0.57    inference(cnf_transformation,[],[f36])).
% 0.21/0.57  fof(f486,plain,(
% 0.21/0.57    ~spl9_10 | ~spl9_12),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f485])).
% 0.21/0.57  fof(f485,plain,(
% 0.21/0.57    $false | (~spl9_10 | ~spl9_12)),
% 0.21/0.57    inference(subsumption_resolution,[],[f484,f86])).
% 0.21/0.57  fof(f86,plain,(
% 0.21/0.57    ( ! [X1] : (~sP0(k1_xboole_0,X1)) )),
% 0.21/0.57    inference(equality_resolution,[],[f72])).
% 0.21/0.57  fof(f72,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k1_xboole_0 != X0 | ~sP0(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f44])).
% 0.21/0.57  fof(f44,plain,(
% 0.21/0.57    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 0.21/0.57    inference(nnf_transformation,[],[f27])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 0.21/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.57  fof(f484,plain,(
% 0.21/0.57    sP0(k1_xboole_0,k1_xboole_0) | (~spl9_10 | ~spl9_12)),
% 0.21/0.57    inference(backward_demodulation,[],[f449,f476])).
% 0.21/0.57  fof(f476,plain,(
% 0.21/0.57    k1_xboole_0 = sK5 | ~spl9_12),
% 0.21/0.57    inference(avatar_component_clause,[],[f474])).
% 0.21/0.57  fof(f474,plain,(
% 0.21/0.57    spl9_12 <=> k1_xboole_0 = sK5),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 0.21/0.57  fof(f449,plain,(
% 0.21/0.57    sP0(sK5,k1_xboole_0) | ~spl9_10),
% 0.21/0.57    inference(backward_demodulation,[],[f404,f434])).
% 0.21/0.57  fof(f434,plain,(
% 0.21/0.57    k1_xboole_0 = sK6 | ~spl9_10),
% 0.21/0.57    inference(resolution,[],[f404,f71])).
% 0.21/0.57  fof(f71,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~sP0(X0,X1) | k1_xboole_0 = X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f44])).
% 0.21/0.57  fof(f404,plain,(
% 0.21/0.57    sP0(sK5,sK6) | ~spl9_10),
% 0.21/0.57    inference(avatar_component_clause,[],[f402])).
% 0.21/0.57  fof(f402,plain,(
% 0.21/0.57    spl9_10 <=> sP0(sK5,sK6)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 0.21/0.57  fof(f477,plain,(
% 0.21/0.57    spl9_11 | spl9_12 | ~spl9_10),
% 0.21/0.57    inference(avatar_split_clause,[],[f468,f402,f474,f470])).
% 0.21/0.57  fof(f468,plain,(
% 0.21/0.57    k1_xboole_0 = sK5 | k1_xboole_0 = sK7 | ~spl9_10),
% 0.21/0.57    inference(subsumption_resolution,[],[f467,f436])).
% 0.21/0.57  fof(f436,plain,(
% 0.21/0.57    v1_funct_2(sK7,sK5,k1_xboole_0) | ~spl9_10),
% 0.21/0.57    inference(backward_demodulation,[],[f52,f434])).
% 0.21/0.57  fof(f52,plain,(
% 0.21/0.57    v1_funct_2(sK7,sK5,sK6)),
% 0.21/0.57    inference(cnf_transformation,[],[f36])).
% 0.21/0.57  fof(f467,plain,(
% 0.21/0.57    ~v1_funct_2(sK7,sK5,k1_xboole_0) | k1_xboole_0 = sK5 | k1_xboole_0 = sK7 | ~spl9_10),
% 0.21/0.57    inference(resolution,[],[f443,f85])).
% 0.21/0.57  fof(f85,plain,(
% 0.21/0.57    ( ! [X2,X0] : (~sP2(X0,k1_xboole_0,X2) | ~v1_funct_2(X0,X2,k1_xboole_0) | k1_xboole_0 = X2 | k1_xboole_0 = X0) )),
% 0.21/0.57    inference(equality_resolution,[],[f67])).
% 0.21/0.57  fof(f67,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~v1_funct_2(X0,X2,X1) | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP2(X0,X1,X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f41])).
% 0.21/0.57  fof(f41,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (((v1_funct_2(X0,X2,X1) | k1_xboole_0 != X0) & (k1_xboole_0 = X0 | ~v1_funct_2(X0,X2,X1))) | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP2(X0,X1,X2))),
% 0.21/0.57    inference(rectify,[],[f40])).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    ! [X2,X1,X0] : (((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP2(X2,X1,X0))),
% 0.21/0.57    inference(nnf_transformation,[],[f29])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP2(X2,X1,X0))),
% 0.21/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.57  fof(f443,plain,(
% 0.21/0.57    sP2(sK7,k1_xboole_0,sK5) | ~spl9_10),
% 0.21/0.57    inference(backward_demodulation,[],[f115,f434])).
% 0.21/0.57  fof(f115,plain,(
% 0.21/0.57    sP2(sK7,sK6,sK5)),
% 0.21/0.57    inference(resolution,[],[f74,f53])).
% 0.21/0.57  fof(f74,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP2(X2,X1,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f30])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((sP2(X2,X1,X0) & sP1(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(definition_folding,[],[f22,f29,f28,f27])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 0.21/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(flattening,[],[f21])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(ennf_transformation,[],[f9])).
% 0.21/0.57  fof(f9,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.57  fof(f433,plain,(
% 0.21/0.57    ~spl9_7 | ~spl9_9),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f432])).
% 0.21/0.57  fof(f432,plain,(
% 0.21/0.57    $false | (~spl9_7 | ~spl9_9)),
% 0.21/0.57    inference(subsumption_resolution,[],[f426,f134])).
% 0.21/0.57  fof(f426,plain,(
% 0.21/0.57    r1_tarski(k2_relat_1(sK7),sK4) | (~spl9_7 | ~spl9_9)),
% 0.21/0.57    inference(resolution,[],[f425,f157])).
% 0.21/0.57  fof(f157,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~sP3(X0,X1,X2) | r1_tarski(k2_relat_1(X2),X0)) )),
% 0.21/0.57    inference(resolution,[],[f142,f61])).
% 0.21/0.57  fof(f142,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(X1)) | ~sP3(X1,X2,X0)) )),
% 0.21/0.57    inference(resolution,[],[f140,f77])).
% 0.21/0.57  fof(f77,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~sP3(X0,X1,X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f46])).
% 0.21/0.57  fof(f46,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X2,X1,X0) & v1_funct_1(X2)) | ~sP3(X0,X1,X2))),
% 0.21/0.57    inference(rectify,[],[f45])).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    ! [X1,X0,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~sP3(X1,X0,X2))),
% 0.21/0.57    inference(nnf_transformation,[],[f31])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ! [X1,X0,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~sP3(X1,X0,X2))),
% 0.21/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.21/0.57  fof(f425,plain,(
% 0.21/0.57    sP3(sK4,sK5,sK7) | (~spl9_7 | ~spl9_9)),
% 0.21/0.57    inference(forward_demodulation,[],[f275,f400])).
% 0.21/0.57  fof(f400,plain,(
% 0.21/0.57    sK5 = k1_relat_1(sK7) | ~spl9_9),
% 0.21/0.57    inference(avatar_component_clause,[],[f398])).
% 0.21/0.57  fof(f398,plain,(
% 0.21/0.57    spl9_9 <=> sK5 = k1_relat_1(sK7)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 0.21/0.57  fof(f275,plain,(
% 0.21/0.57    sP3(sK4,k1_relat_1(sK7),sK7) | ~spl9_7),
% 0.21/0.57    inference(avatar_component_clause,[],[f273])).
% 0.21/0.57  fof(f273,plain,(
% 0.21/0.57    spl9_7 <=> sP3(sK4,k1_relat_1(sK7),sK7)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.21/0.57  fof(f423,plain,(
% 0.21/0.57    spl9_8 | ~spl9_9),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f422])).
% 0.21/0.57  fof(f422,plain,(
% 0.21/0.57    $false | (spl9_8 | ~spl9_9)),
% 0.21/0.57    inference(subsumption_resolution,[],[f416,f134])).
% 0.21/0.57  fof(f416,plain,(
% 0.21/0.57    r1_tarski(k2_relat_1(sK7),sK4) | (spl9_8 | ~spl9_9)),
% 0.21/0.57    inference(resolution,[],[f415,f157])).
% 0.21/0.57  fof(f415,plain,(
% 0.21/0.57    sP3(sK4,sK5,sK7) | (spl9_8 | ~spl9_9)),
% 0.21/0.57    inference(resolution,[],[f413,f406])).
% 0.21/0.57  fof(f406,plain,(
% 0.21/0.57    ~r2_hidden(sK8(sK5,sK4,sK7),sK5) | (spl9_8 | ~spl9_9)),
% 0.21/0.57    inference(backward_demodulation,[],[f281,f400])).
% 0.21/0.57  fof(f281,plain,(
% 0.21/0.57    ~r2_hidden(sK8(k1_relat_1(sK7),sK4,sK7),sK5) | spl9_8),
% 0.21/0.57    inference(resolution,[],[f279,f57])).
% 0.21/0.57  fof(f57,plain,(
% 0.21/0.57    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f16])).
% 0.21/0.57  fof(f16,plain,(
% 0.21/0.57    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.57  fof(f279,plain,(
% 0.21/0.57    ~m1_subset_1(sK8(k1_relat_1(sK7),sK4,sK7),sK5) | spl9_8),
% 0.21/0.57    inference(avatar_component_clause,[],[f277])).
% 0.21/0.57  fof(f277,plain,(
% 0.21/0.57    spl9_8 <=> m1_subset_1(sK8(k1_relat_1(sK7),sK4,sK7),sK5)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.21/0.57  fof(f413,plain,(
% 0.21/0.57    ( ! [X1] : (r2_hidden(sK8(sK5,X1,sK7),sK5) | sP3(X1,sK5,sK7)) ) | ~spl9_9),
% 0.21/0.57    inference(subsumption_resolution,[],[f412,f92])).
% 0.21/0.57  fof(f92,plain,(
% 0.21/0.57    v1_relat_1(sK7)),
% 0.21/0.57    inference(resolution,[],[f63,f53])).
% 0.21/0.57  fof(f63,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f17,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(ennf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.57  fof(f412,plain,(
% 0.21/0.57    ( ! [X1] : (r2_hidden(sK8(sK5,X1,sK7),sK5) | sP3(X1,sK5,sK7) | ~v1_relat_1(sK7)) ) | ~spl9_9),
% 0.21/0.57    inference(subsumption_resolution,[],[f409,f51])).
% 0.21/0.57  fof(f51,plain,(
% 0.21/0.57    v1_funct_1(sK7)),
% 0.21/0.57    inference(cnf_transformation,[],[f36])).
% 0.21/0.57  fof(f409,plain,(
% 0.21/0.57    ( ! [X1] : (r2_hidden(sK8(sK5,X1,sK7),sK5) | sP3(X1,sK5,sK7) | ~v1_funct_1(sK7) | ~v1_relat_1(sK7)) ) | ~spl9_9),
% 0.21/0.57    inference(superposition,[],[f88,f400])).
% 0.21/0.57  fof(f88,plain,(
% 0.21/0.57    ( ! [X2,X1] : (r2_hidden(sK8(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | sP3(X1,k1_relat_1(X2),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.57    inference(equality_resolution,[],[f78])).
% 0.21/0.57  fof(f78,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (sP3(X1,X0,X2) | r2_hidden(sK8(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f48])).
% 0.21/0.57  fof(f48,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (sP3(X1,X0,X2) | (~r2_hidden(k1_funct_1(X2,sK8(X0,X1,X2)),X1) & r2_hidden(sK8(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f32,f47])).
% 0.21/0.57  fof(f47,plain,(
% 0.21/0.57    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK8(X0,X1,X2)),X1) & r2_hidden(sK8(X0,X1,X2),X0)))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (sP3(X1,X0,X2) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.57    inference(definition_folding,[],[f24,f31])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.57    inference(flattening,[],[f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.57    inference(ennf_transformation,[],[f11])).
% 0.21/0.57  fof(f11,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).
% 0.21/0.57  fof(f405,plain,(
% 0.21/0.57    spl9_9 | spl9_10),
% 0.21/0.57    inference(avatar_split_clause,[],[f396,f402,f398])).
% 0.21/0.57  fof(f396,plain,(
% 0.21/0.57    sP0(sK5,sK6) | sK5 = k1_relat_1(sK7)),
% 0.21/0.57    inference(subsumption_resolution,[],[f394,f52])).
% 0.21/0.57  fof(f394,plain,(
% 0.21/0.57    ~v1_funct_2(sK7,sK5,sK6) | sP0(sK5,sK6) | sK5 = k1_relat_1(sK7)),
% 0.21/0.57    inference(resolution,[],[f186,f53])).
% 0.21/0.57  fof(f186,plain,(
% 0.21/0.57    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4) | sP0(X3,X4) | k1_relat_1(X5) = X3) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f184,f73])).
% 0.21/0.57  fof(f73,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP1(X0,X2,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f30])).
% 0.21/0.57  fof(f184,plain,(
% 0.21/0.57    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4) | sP0(X3,X4) | ~sP1(X3,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.21/0.57    inference(superposition,[],[f69,f64])).
% 0.21/0.57  fof(f64,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f18])).
% 0.21/0.57  fof(f18,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(ennf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.57  fof(f69,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP0(X0,X2) | ~sP1(X0,X1,X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f43])).
% 0.21/0.57  fof(f43,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP0(X0,X2) | ~sP1(X0,X1,X2))),
% 0.21/0.57    inference(rectify,[],[f42])).
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 0.21/0.57    inference(nnf_transformation,[],[f28])).
% 0.21/0.57  fof(f280,plain,(
% 0.21/0.57    spl9_7 | ~spl9_8),
% 0.21/0.57    inference(avatar_split_clause,[],[f271,f277,f273])).
% 0.21/0.57  fof(f271,plain,(
% 0.21/0.57    ~m1_subset_1(sK8(k1_relat_1(sK7),sK4,sK7),sK5) | sP3(sK4,k1_relat_1(sK7),sK7)),
% 0.21/0.57    inference(subsumption_resolution,[],[f270,f92])).
% 0.21/0.57  fof(f270,plain,(
% 0.21/0.57    ~m1_subset_1(sK8(k1_relat_1(sK7),sK4,sK7),sK5) | sP3(sK4,k1_relat_1(sK7),sK7) | ~v1_relat_1(sK7)),
% 0.21/0.57    inference(subsumption_resolution,[],[f269,f51])).
% 0.21/0.57  fof(f269,plain,(
% 0.21/0.57    ~m1_subset_1(sK8(k1_relat_1(sK7),sK4,sK7),sK5) | sP3(sK4,k1_relat_1(sK7),sK7) | ~v1_funct_1(sK7) | ~v1_relat_1(sK7)),
% 0.21/0.57    inference(resolution,[],[f268,f87])).
% 0.21/0.57  fof(f87,plain,(
% 0.21/0.57    ( ! [X2,X1] : (~r2_hidden(k1_funct_1(X2,sK8(k1_relat_1(X2),X1,X2)),X1) | sP3(X1,k1_relat_1(X2),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.57    inference(equality_resolution,[],[f79])).
% 0.21/0.57  fof(f79,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (sP3(X1,X0,X2) | ~r2_hidden(k1_funct_1(X2,sK8(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f48])).
% 0.21/0.57  fof(f268,plain,(
% 0.21/0.57    ( ! [X0] : (r2_hidden(k1_funct_1(sK7,X0),sK4) | ~m1_subset_1(X0,sK5)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f267,f49])).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    ~v1_xboole_0(sK5)),
% 0.21/0.57    inference(cnf_transformation,[],[f36])).
% 0.21/0.57  fof(f267,plain,(
% 0.21/0.57    ( ! [X0] : (r2_hidden(k1_funct_1(sK7,X0),sK4) | ~m1_subset_1(X0,sK5) | v1_xboole_0(sK5)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f266,f51])).
% 0.21/0.57  fof(f266,plain,(
% 0.21/0.57    ( ! [X0] : (r2_hidden(k1_funct_1(sK7,X0),sK4) | ~m1_subset_1(X0,sK5) | ~v1_funct_1(sK7) | v1_xboole_0(sK5)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f265,f52])).
% 0.21/0.57  fof(f265,plain,(
% 0.21/0.57    ( ! [X0] : (r2_hidden(k1_funct_1(sK7,X0),sK4) | ~m1_subset_1(X0,sK5) | ~v1_funct_2(sK7,sK5,sK6) | ~v1_funct_1(sK7) | v1_xboole_0(sK5)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f264,f53])).
% 0.21/0.57  fof(f264,plain,(
% 0.21/0.57    ( ! [X0] : (r2_hidden(k1_funct_1(sK7,X0),sK4) | ~m1_subset_1(X0,sK5) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) | ~v1_funct_2(sK7,sK5,sK6) | ~v1_funct_1(sK7) | v1_xboole_0(sK5)) )),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f263])).
% 0.21/0.57  fof(f263,plain,(
% 0.21/0.57    ( ! [X0] : (r2_hidden(k1_funct_1(sK7,X0),sK4) | ~m1_subset_1(X0,sK5) | ~m1_subset_1(X0,sK5) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) | ~v1_funct_2(sK7,sK5,sK6) | ~v1_funct_1(sK7) | v1_xboole_0(sK5)) )),
% 0.21/0.57    inference(superposition,[],[f54,f80])).
% 0.21/0.57  fof(f80,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f26])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.21/0.57    inference(flattening,[],[f25])).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.21/0.57  fof(f54,plain,(
% 0.21/0.57    ( ! [X4] : (r2_hidden(k3_funct_2(sK5,sK6,sK7,X4),sK4) | ~m1_subset_1(X4,sK5)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f36])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (7428)------------------------------
% 0.21/0.57  % (7428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (7428)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (7428)Memory used [KB]: 6396
% 0.21/0.57  % (7428)Time elapsed: 0.119 s
% 0.21/0.57  % (7428)------------------------------
% 0.21/0.57  % (7428)------------------------------
% 0.21/0.57  % (7423)Success in time 0.211 s
%------------------------------------------------------------------------------
