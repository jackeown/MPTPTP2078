%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 174 expanded)
%              Number of leaves         :   25 (  59 expanded)
%              Depth                    :   17
%              Number of atoms          :  382 ( 629 expanded)
%              Number of equality atoms :   46 (  76 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f176,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f70,f74,f82,f90,f95,f100,f152,f158,f165,f169,f175])).

fof(f175,plain,
    ( ~ spl5_2
    | ~ spl5_9 ),
    inference(avatar_contradiction_clause,[],[f174])).

fof(f174,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f69,f145])).

fof(f145,plain,
    ( ! [X2,X3] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl5_9
  <=> ! [X3,X2] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f69,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl5_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f169,plain,
    ( ~ spl5_2
    | ~ spl5_13 ),
    inference(avatar_contradiction_clause,[],[f168])).

fof(f168,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f69,f166])).

fof(f166,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ spl5_13 ),
    inference(resolution,[],[f163,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f163,plain,
    ( ! [X0] : ~ v4_relat_1(sK3,X0)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl5_13
  <=> ! [X0] : ~ v4_relat_1(sK3,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f165,plain,
    ( spl5_13
    | ~ spl5_5
    | ~ spl5_4
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f160,f150,f80,f85,f162])).

fof(f85,plain,
    ( spl5_5
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f80,plain,
    ( spl5_4
  <=> r2_hidden(sK0,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f150,plain,
    ( spl5_11
  <=> ! [X0,X4] :
        ( sK0 != X0
        | ~ r2_hidden(X0,k9_relat_1(sK3,X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f160,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,k2_relat_1(sK3))
        | ~ v1_relat_1(sK3)
        | ~ v4_relat_1(sK3,X0) )
    | ~ spl5_11 ),
    inference(superposition,[],[f159,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X0,X1) = k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X0,X1) = k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f46,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f159,plain,
    ( ! [X0] : ~ r2_hidden(sK0,k9_relat_1(sK3,X0))
    | ~ spl5_11 ),
    inference(equality_resolution,[],[f151])).

fof(f151,plain,
    ( ! [X4,X0] :
        ( sK0 != X0
        | ~ r2_hidden(X0,k9_relat_1(sK3,X4)) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f150])).

fof(f158,plain,
    ( ~ spl5_2
    | ~ spl5_10 ),
    inference(avatar_contradiction_clause,[],[f157])).

fof(f157,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f69,f148])).

fof(f148,plain,
    ( ! [X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl5_10
  <=> ! [X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f152,plain,
    ( ~ spl5_5
    | spl5_9
    | spl5_10
    | spl5_11
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f142,f98,f150,f147,f144,f85])).

fof(f98,plain,
    ( spl5_7
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | k1_funct_1(sK3,sK4(X0,X1,sK3)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f142,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( sK0 != X0
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ r2_hidden(X0,k9_relat_1(sK3,X4))
        | ~ v1_relat_1(sK3) )
    | ~ spl5_7 ),
    inference(duplicate_literal_removal,[],[f138])).

fof(f138,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( sK0 != X0
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ r2_hidden(X0,k9_relat_1(sK3,X4))
        | ~ r2_hidden(X0,k9_relat_1(sK3,X4))
        | ~ v1_relat_1(sK3) )
    | ~ spl5_7 ),
    inference(resolution,[],[f134,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2)
            & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2)
        & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f134,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ r2_hidden(sK4(X0,X1,sK3),k1_relat_1(X2))
        | sK0 != X0
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X3)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ r2_hidden(X0,k9_relat_1(sK3,X1)) )
    | ~ spl5_7 ),
    inference(resolution,[],[f115,f45])).

fof(f45,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f115,plain,
    ( ! [X6,X8,X7,X5,X9] :
        ( ~ v1_relat_1(X9)
        | sK0 != X5
        | ~ r2_hidden(sK4(X5,X6,sK3),k1_relat_1(X7))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK1,X8)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(X9))
        | ~ r2_hidden(X5,k9_relat_1(sK3,X6)) )
    | ~ spl5_7 ),
    inference(resolution,[],[f107,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f107,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_relat_1(X2)
        | ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | sK0 != X0
        | ~ r2_hidden(sK4(X0,X1,sK3),k1_relat_1(X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X3))) )
    | ~ spl5_7 ),
    inference(resolution,[],[f106,f57])).

fof(f106,plain,
    ( ! [X4,X5,X3] :
        ( ~ v4_relat_1(X5,sK1)
        | ~ r2_hidden(sK4(X3,X4,sK3),k1_relat_1(X5))
        | ~ r2_hidden(X3,k9_relat_1(sK3,X4))
        | sK0 != X3
        | ~ v1_relat_1(X5) )
    | ~ spl5_7 ),
    inference(resolution,[],[f103,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f103,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X2,sK1)
        | sK0 != X0
        | ~ r2_hidden(sK4(X0,X1,sK3),X2)
        | ~ r2_hidden(X0,k9_relat_1(sK3,X1)) )
    | ~ spl5_7 ),
    inference(resolution,[],[f102,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f102,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(sK1))
        | ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | sK0 != X0
        | ~ r2_hidden(sK4(X0,X1,sK3),X2) )
    | ~ spl5_7 ),
    inference(resolution,[],[f101,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f101,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4(X0,X1,sK3),sK1)
        | sK0 != X0
        | ~ r2_hidden(X0,k9_relat_1(sK3,X1)) )
    | ~ spl5_7 ),
    inference(superposition,[],[f43,f99])).

fof(f99,plain,
    ( ! [X0,X1] :
        ( k1_funct_1(sK3,sK4(X0,X1,sK3)) = X0
        | ~ r2_hidden(X0,k9_relat_1(sK3,X1)) )
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f98])).

fof(f43,plain,(
    ! [X4] :
      ( sK0 != k1_funct_1(sK3,X4)
      | ~ m1_subset_1(X4,sK1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ! [X4] :
        ( sK0 != k1_funct_1(sK3,X4)
        | ~ m1_subset_1(X4,sK1) )
    & r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f30])).

fof(f30,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( k1_funct_1(X3,X4) != X0
            | ~ m1_subset_1(X4,X1) )
        & r2_hidden(X0,k2_relset_1(X1,X2,X3))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X3) )
   => ( ! [X4] :
          ( sK0 != k1_funct_1(sK3,X4)
          | ~ m1_subset_1(X4,sK1) )
      & r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ( m1_subset_1(X4,X1)
             => k1_funct_1(X3,X4) != X0 )
          & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).

fof(f100,plain,
    ( ~ spl5_5
    | spl5_7
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f96,f88,f98,f85])).

fof(f88,plain,
    ( spl5_6
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK3)
        | k1_funct_1(sK3,X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f96,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | ~ v1_relat_1(sK3)
        | k1_funct_1(sK3,sK4(X0,X1,sK3)) = X0 )
    | ~ spl5_6 ),
    inference(resolution,[],[f53,f89])).

fof(f89,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK3)
        | k1_funct_1(sK3,X0) = X1 )
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f95,plain,
    ( ~ spl5_2
    | spl5_5 ),
    inference(avatar_contradiction_clause,[],[f94])).

fof(f94,plain,
    ( $false
    | ~ spl5_2
    | spl5_5 ),
    inference(subsumption_resolution,[],[f69,f92])).

fof(f92,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl5_5 ),
    inference(resolution,[],[f91,f45])).

fof(f91,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(X0)) )
    | spl5_5 ),
    inference(resolution,[],[f86,f44])).

fof(f86,plain,
    ( ~ v1_relat_1(sK3)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f90,plain,
    ( ~ spl5_5
    | spl5_6
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f83,f72,f88,f85])).

fof(f72,plain,
    ( spl5_3
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f83,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK3)
        | k1_funct_1(sK3,X0) = X1
        | ~ v1_relat_1(sK3) )
    | ~ spl5_3 ),
    inference(resolution,[],[f59,f73])).

fof(f73,plain,
    ( v1_funct_1(sK3)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f82,plain,
    ( ~ spl5_2
    | spl5_4
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f77,f64,f80,f68])).

fof(f64,plain,
    ( spl5_1
  <=> r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f77,plain,
    ( r2_hidden(sK0,k2_relat_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_1 ),
    inference(superposition,[],[f65,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f65,plain,
    ( r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f74,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f40,f72])).

fof(f40,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f70,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f41,f68])).

fof(f41,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f31])).

fof(f66,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f42,f64])).

fof(f42,plain,(
    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:41:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (7679)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (7673)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (7671)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (7680)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (7672)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (7671)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (7681)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f176,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f66,f70,f74,f82,f90,f95,f100,f152,f158,f165,f169,f175])).
% 0.21/0.52  fof(f175,plain,(
% 0.21/0.52    ~spl5_2 | ~spl5_9),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f174])).
% 0.21/0.52  fof(f174,plain,(
% 0.21/0.52    $false | (~spl5_2 | ~spl5_9)),
% 0.21/0.52    inference(subsumption_resolution,[],[f69,f145])).
% 0.21/0.52  fof(f145,plain,(
% 0.21/0.52    ( ! [X2,X3] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) ) | ~spl5_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f144])).
% 0.21/0.52  fof(f144,plain,(
% 0.21/0.52    spl5_9 <=> ! [X3,X2] : ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f68])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    spl5_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.52  fof(f169,plain,(
% 0.21/0.52    ~spl5_2 | ~spl5_13),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f168])).
% 0.21/0.52  fof(f168,plain,(
% 0.21/0.52    $false | (~spl5_2 | ~spl5_13)),
% 0.21/0.52    inference(subsumption_resolution,[],[f69,f166])).
% 0.21/0.52  fof(f166,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl5_13),
% 0.21/0.52    inference(resolution,[],[f163,f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.52  fof(f163,plain,(
% 0.21/0.52    ( ! [X0] : (~v4_relat_1(sK3,X0)) ) | ~spl5_13),
% 0.21/0.52    inference(avatar_component_clause,[],[f162])).
% 0.21/0.52  fof(f162,plain,(
% 0.21/0.52    spl5_13 <=> ! [X0] : ~v4_relat_1(sK3,X0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.52  fof(f165,plain,(
% 0.21/0.52    spl5_13 | ~spl5_5 | ~spl5_4 | ~spl5_11),
% 0.21/0.52    inference(avatar_split_clause,[],[f160,f150,f80,f85,f162])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    spl5_5 <=> v1_relat_1(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    spl5_4 <=> r2_hidden(sK0,k2_relat_1(sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    spl5_11 <=> ! [X0,X4] : (sK0 != X0 | ~r2_hidden(X0,k9_relat_1(sK3,X4)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.52  fof(f160,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(sK0,k2_relat_1(sK3)) | ~v1_relat_1(sK3) | ~v4_relat_1(sK3,X0)) ) | ~spl5_11),
% 0.21/0.52    inference(superposition,[],[f159,f76])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k9_relat_1(X0,X1) = k2_relat_1(X0) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f75])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k9_relat_1(X0,X1) = k2_relat_1(X0) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(superposition,[],[f46,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.52  fof(f159,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(sK0,k9_relat_1(sK3,X0))) ) | ~spl5_11),
% 0.21/0.52    inference(equality_resolution,[],[f151])).
% 0.21/0.52  fof(f151,plain,(
% 0.21/0.52    ( ! [X4,X0] : (sK0 != X0 | ~r2_hidden(X0,k9_relat_1(sK3,X4))) ) | ~spl5_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f150])).
% 0.21/0.52  fof(f158,plain,(
% 0.21/0.52    ~spl5_2 | ~spl5_10),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f157])).
% 0.21/0.52  fof(f157,plain,(
% 0.21/0.52    $false | (~spl5_2 | ~spl5_10)),
% 0.21/0.52    inference(subsumption_resolution,[],[f69,f148])).
% 0.21/0.52  fof(f148,plain,(
% 0.21/0.52    ( ! [X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))) ) | ~spl5_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f147])).
% 0.21/0.52  fof(f147,plain,(
% 0.21/0.52    spl5_10 <=> ! [X1] : ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.52  fof(f152,plain,(
% 0.21/0.52    ~spl5_5 | spl5_9 | spl5_10 | spl5_11 | ~spl5_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f142,f98,f150,f147,f144,f85])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    spl5_7 <=> ! [X1,X0] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | k1_funct_1(sK3,sK4(X0,X1,sK3)) = X0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.52  fof(f142,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (sK0 != X0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~r2_hidden(X0,k9_relat_1(sK3,X4)) | ~v1_relat_1(sK3)) ) | ~spl5_7),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f138])).
% 0.21/0.52  fof(f138,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (sK0 != X0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~r2_hidden(X0,k9_relat_1(sK3,X4)) | ~r2_hidden(X0,k9_relat_1(sK3,X4)) | ~v1_relat_1(sK3)) ) | ~spl5_7),
% 0.21/0.52    inference(resolution,[],[f134,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2) & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2) & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(rectify,[],[f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(nnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 0.21/0.52  fof(f134,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_hidden(sK4(X0,X1,sK3),k1_relat_1(X2)) | sK0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~r2_hidden(X0,k9_relat_1(sK3,X1))) ) | ~spl5_7),
% 0.21/0.52    inference(resolution,[],[f115,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    ( ! [X6,X8,X7,X5,X9] : (~v1_relat_1(X9) | sK0 != X5 | ~r2_hidden(sK4(X5,X6,sK3),k1_relat_1(X7)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK1,X8))) | ~m1_subset_1(X7,k1_zfmisc_1(X9)) | ~r2_hidden(X5,k9_relat_1(sK3,X6))) ) | ~spl5_7),
% 0.21/0.52    inference(resolution,[],[f107,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(sK3,X1)) | sK0 != X0 | ~r2_hidden(sK4(X0,X1,sK3),k1_relat_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X3)))) ) | ~spl5_7),
% 0.21/0.52    inference(resolution,[],[f106,f57])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    ( ! [X4,X5,X3] : (~v4_relat_1(X5,sK1) | ~r2_hidden(sK4(X3,X4,sK3),k1_relat_1(X5)) | ~r2_hidden(X3,k9_relat_1(sK3,X4)) | sK0 != X3 | ~v1_relat_1(X5)) ) | ~spl5_7),
% 0.21/0.52    inference(resolution,[],[f103,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X2,sK1) | sK0 != X0 | ~r2_hidden(sK4(X0,X1,sK3),X2) | ~r2_hidden(X0,k9_relat_1(sK3,X1))) ) | ~spl5_7),
% 0.21/0.52    inference(resolution,[],[f102,f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.52    inference(nnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.52  fof(f102,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(sK1)) | ~r2_hidden(X0,k9_relat_1(sK3,X1)) | sK0 != X0 | ~r2_hidden(sK4(X0,X1,sK3),X2)) ) | ~spl5_7),
% 0.21/0.52    inference(resolution,[],[f101,f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.52    inference(flattening,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(sK4(X0,X1,sK3),sK1) | sK0 != X0 | ~r2_hidden(X0,k9_relat_1(sK3,X1))) ) | ~spl5_7),
% 0.21/0.52    inference(superposition,[],[f43,f99])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_funct_1(sK3,sK4(X0,X1,sK3)) = X0 | ~r2_hidden(X0,k9_relat_1(sK3,X1))) ) | ~spl5_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f98])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X4] : (sK0 != k1_funct_1(sK3,X4) | ~m1_subset_1(X4,sK1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X4] : (sK0 != k1_funct_1(sK3,X4) | ~m1_subset_1(X4,sK1)) & r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(sK3)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X3)) => (! [X4] : (sK0 != k1_funct_1(sK3,X4) | ~m1_subset_1(X4,sK1)) & r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(sK3))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X3))),
% 0.21/0.52    inference(flattening,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X3)))),
% 0.21/0.52    inference(ennf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f13])).
% 0.21/0.52  fof(f13,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.21/0.52    inference(negated_conjecture,[],[f12])).
% 0.21/0.52  fof(f12,conjecture,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    ~spl5_5 | spl5_7 | ~spl5_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f96,f88,f98,f85])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    spl5_6 <=> ! [X1,X0] : (~r2_hidden(k4_tarski(X0,X1),sK3) | k1_funct_1(sK3,X0) = X1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | ~v1_relat_1(sK3) | k1_funct_1(sK3,sK4(X0,X1,sK3)) = X0) ) | ~spl5_6),
% 0.21/0.52    inference(resolution,[],[f53,f89])).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK3) | k1_funct_1(sK3,X0) = X1) ) | ~spl5_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f88])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    ~spl5_2 | spl5_5),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f94])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    $false | (~spl5_2 | spl5_5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f69,f92])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl5_5),
% 0.21/0.52    inference(resolution,[],[f91,f45])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_relat_1(X0) | ~m1_subset_1(sK3,k1_zfmisc_1(X0))) ) | spl5_5),
% 0.21/0.52    inference(resolution,[],[f86,f44])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    ~v1_relat_1(sK3) | spl5_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f85])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    ~spl5_5 | spl5_6 | ~spl5_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f83,f72,f88,f85])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    spl5_3 <=> v1_funct_1(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK3) | k1_funct_1(sK3,X0) = X1 | ~v1_relat_1(sK3)) ) | ~spl5_3),
% 0.21/0.52    inference(resolution,[],[f59,f73])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    v1_funct_1(sK3) | ~spl5_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f72])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(flattening,[],[f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(nnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(flattening,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    ~spl5_2 | spl5_4 | ~spl5_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f77,f64,f80,f68])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    spl5_1 <=> r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    r2_hidden(sK0,k2_relat_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_1),
% 0.21/0.52    inference(superposition,[],[f65,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) | ~spl5_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f64])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    spl5_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f40,f72])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    v1_funct_1(sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    spl5_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f41,f68])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    spl5_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f42,f64])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (7671)------------------------------
% 0.21/0.52  % (7671)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (7671)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (7671)Memory used [KB]: 10746
% 0.21/0.52  % (7671)Time elapsed: 0.073 s
% 0.21/0.52  % (7671)------------------------------
% 0.21/0.52  % (7671)------------------------------
% 0.21/0.52  % (7664)Success in time 0.157 s
%------------------------------------------------------------------------------
