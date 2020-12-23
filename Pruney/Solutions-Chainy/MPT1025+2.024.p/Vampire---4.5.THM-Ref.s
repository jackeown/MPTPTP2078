%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 237 expanded)
%              Number of leaves         :   34 (  97 expanded)
%              Depth                    :   12
%              Number of atoms          :  537 (1103 expanded)
%              Number of equality atoms :   95 ( 203 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1445,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f101,f105,f109,f115,f205,f231,f234,f244,f327,f543,f591,f611,f669,f1407,f1432])).

fof(f1432,plain,
    ( ~ spl10_15
    | ~ spl10_11
    | ~ spl10_18
    | ~ spl10_62 ),
    inference(avatar_split_clause,[],[f1138,f667,f325,f203,f242])).

fof(f242,plain,
    ( spl10_15
  <=> r2_hidden(sK7(sK3,sK2,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f203,plain,
    ( spl10_11
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f325,plain,
    ( spl10_18
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | k1_funct_1(sK3,sK7(sK3,X1,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f667,plain,
    ( spl10_62
  <=> ! [X5,X4] :
        ( r2_hidden(sK7(sK3,X4,X5),sK0)
        | ~ r2_hidden(X5,k9_relat_1(sK3,X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_62])])).

fof(f1138,plain,
    ( ~ r2_hidden(sK7(sK3,sK2,sK4),sK2)
    | ~ spl10_11
    | ~ spl10_18
    | ~ spl10_62 ),
    inference(resolution,[],[f696,f204])).

fof(f204,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f203])).

fof(f696,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK4,k9_relat_1(sK3,X2))
        | ~ r2_hidden(sK7(sK3,X2,sK4),sK2) )
    | ~ spl10_18
    | ~ spl10_62 ),
    inference(subsumption_resolution,[],[f332,f668])).

fof(f668,plain,
    ( ! [X4,X5] :
        ( r2_hidden(sK7(sK3,X4,X5),sK0)
        | ~ r2_hidden(X5,k9_relat_1(sK3,X4)) )
    | ~ spl10_62 ),
    inference(avatar_component_clause,[],[f667])).

fof(f332,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK7(sK3,X2,sK4),sK0)
        | ~ r2_hidden(sK4,k9_relat_1(sK3,X2))
        | ~ r2_hidden(sK7(sK3,X2,sK4),sK2) )
    | ~ spl10_18 ),
    inference(resolution,[],[f329,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f329,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK7(sK3,X0,sK4),sK0)
        | ~ r2_hidden(sK7(sK3,X0,sK4),sK2)
        | ~ r2_hidden(sK4,k9_relat_1(sK3,X0)) )
    | ~ spl10_18 ),
    inference(equality_resolution,[],[f328])).

fof(f328,plain,
    ( ! [X0,X1] :
        ( sK4 != X1
        | ~ r2_hidden(sK7(sK3,X0,X1),sK2)
        | ~ m1_subset_1(sK7(sK3,X0,X1),sK0)
        | ~ r2_hidden(X1,k9_relat_1(sK3,X0)) )
    | ~ spl10_18 ),
    inference(superposition,[],[f52,f326])).

fof(f326,plain,
    ( ! [X0,X1] :
        ( k1_funct_1(sK3,sK7(sK3,X1,X0)) = X0
        | ~ r2_hidden(X0,k9_relat_1(sK3,X1)) )
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f325])).

fof(f52,plain,(
    ! [X5] :
      ( k1_funct_1(sK3,X5) != sK4
      | ~ r2_hidden(X5,sK2)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ! [X5] :
        ( k1_funct_1(sK3,X5) != sK4
        | ~ r2_hidden(X5,sK2)
        | ~ m1_subset_1(X5,sK0) )
    & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f16,f30,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ m1_subset_1(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK3,X5) != X4
              | ~ r2_hidden(X5,sK2)
              | ~ m1_subset_1(X5,sK0) )
          & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2)) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X4] :
        ( ! [X5] :
            ( k1_funct_1(sK3,X5) != X4
            | ~ r2_hidden(X5,sK2)
            | ~ m1_subset_1(X5,sK0) )
        & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2)) )
   => ( ! [X5] :
          ( k1_funct_1(sK3,X5) != sK4
          | ~ r2_hidden(X5,sK2)
          | ~ m1_subset_1(X5,sK0) )
      & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ( m1_subset_1(X5,X0)
               => ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2) ) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).

fof(f1407,plain,
    ( ~ spl10_5
    | ~ spl10_11
    | ~ spl10_51 ),
    inference(avatar_contradiction_clause,[],[f1406])).

fof(f1406,plain,
    ( $false
    | ~ spl10_5
    | ~ spl10_11
    | ~ spl10_51 ),
    inference(subsumption_resolution,[],[f204,f1401])).

fof(f1401,plain,
    ( ! [X12,X13] : ~ r2_hidden(X12,k9_relat_1(sK3,X13))
    | ~ spl10_5
    | ~ spl10_51 ),
    inference(subsumption_resolution,[],[f1365,f946])).

fof(f946,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3)
    | ~ spl10_5
    | ~ spl10_51 ),
    inference(resolution,[],[f610,f145])).

fof(f145,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
        | ~ r2_hidden(X2,X0) )
    | ~ spl10_5 ),
    inference(resolution,[],[f137,f114])).

fof(f114,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl10_5
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f137,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r2_hidden(X3,X0) ) ),
    inference(resolution,[],[f68,f62])).

fof(f62,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK8(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f39,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK8(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f610,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl10_51 ),
    inference(avatar_component_clause,[],[f609])).

fof(f609,plain,
    ( spl10_51
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_51])])).

fof(f1365,plain,
    ( ! [X12,X13] :
        ( r2_hidden(k4_tarski(sK9(X12,X13,sK3),X12),sK3)
        | ~ r2_hidden(X12,k9_relat_1(sK3,X13)) )
    | ~ spl10_51 ),
    inference(resolution,[],[f157,f610])).

fof(f157,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | r2_hidden(k4_tarski(sK9(X0,X2,X1),X0),X1)
      | ~ r2_hidden(X0,k9_relat_1(X1,X2)) ) ),
    inference(resolution,[],[f72,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK9(X0,X1,X2),X0),X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK9(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK9(X0,X1,X2),X0),X2)
            & r2_hidden(sK9(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f44,f45])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK9(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK9(X0,X1,X2),X0),X2)
        & r2_hidden(sK9(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f669,plain,
    ( ~ spl10_13
    | ~ spl10_4
    | spl10_62
    | ~ spl10_49 ),
    inference(avatar_split_clause,[],[f637,f588,f667,f107,f226])).

fof(f226,plain,
    ( spl10_13
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f107,plain,
    ( spl10_4
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f588,plain,
    ( spl10_49
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_49])])).

fof(f637,plain,
    ( ! [X4,X5] :
        ( r2_hidden(sK7(sK3,X4,X5),sK0)
        | ~ r2_hidden(X5,k9_relat_1(sK3,X4))
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3) )
    | ~ spl10_49 ),
    inference(superposition,[],[f88,f589])).

fof(f589,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl10_49 ),
    inference(avatar_component_clause,[],[f588])).

fof(f88,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK5(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK5(X0,X1,X2),X2) )
              & ( ( sK5(X0,X1,X2) = k1_funct_1(X0,sK6(X0,X1,X2))
                  & r2_hidden(sK6(X0,X1,X2),X1)
                  & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK7(X0,X1,X6)) = X6
                    & r2_hidden(sK7(X0,X1,X6),X1)
                    & r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f33,f36,f35,f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( k1_funct_1(X0,X4) != X3
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X4,k1_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( k1_funct_1(X0,X5) = X3
                & r2_hidden(X5,X1)
                & r2_hidden(X5,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( k1_funct_1(X0,X4) != sK5(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK5(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = sK5(X0,X1,X2)
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( sK5(X0,X1,X2) = k1_funct_1(X0,sK6(X0,X1,X2))
        & r2_hidden(sK6(X0,X1,X2),X1)
        & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK7(X0,X1,X6)) = X6
        & r2_hidden(sK7(X0,X1,X6),X1)
        & r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( k1_funct_1(X0,X5) = X3
                      & r2_hidden(X5,X1)
                      & r2_hidden(X5,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ? [X8] :
                      ( k1_funct_1(X0,X8) = X6
                      & r2_hidden(X8,X1)
                      & r2_hidden(X8,k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) ) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

fof(f611,plain,
    ( spl10_51
    | ~ spl10_2
    | ~ spl10_45 ),
    inference(avatar_split_clause,[],[f594,f538,f99,f609])).

fof(f99,plain,
    ( spl10_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f538,plain,
    ( spl10_45
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_45])])).

fof(f594,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl10_2
    | ~ spl10_45 ),
    inference(superposition,[],[f100,f539])).

fof(f539,plain,
    ( k1_xboole_0 = sK1
    | ~ spl10_45 ),
    inference(avatar_component_clause,[],[f538])).

fof(f100,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f99])).

fof(f591,plain,
    ( ~ spl10_2
    | spl10_49
    | ~ spl10_46 ),
    inference(avatar_split_clause,[],[f586,f541,f588,f99])).

fof(f541,plain,
    ( spl10_46
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_46])])).

fof(f586,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl10_46 ),
    inference(superposition,[],[f76,f542])).

fof(f542,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl10_46 ),
    inference(avatar_component_clause,[],[f541])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f543,plain,
    ( ~ spl10_2
    | spl10_45
    | spl10_46
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f533,f103,f541,f538,f99])).

fof(f103,plain,
    ( spl10_3
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f533,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl10_3 ),
    inference(resolution,[],[f77,f104])).

fof(f104,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f327,plain,
    ( ~ spl10_13
    | spl10_18
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f323,f107,f325,f226])).

fof(f323,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | k1_funct_1(sK3,sK7(sK3,X1,X0)) = X0
        | ~ v1_relat_1(sK3) )
    | ~ spl10_4 ),
    inference(resolution,[],[f86,f108])).

fof(f108,plain,
    ( v1_funct_1(sK3)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f107])).

fof(f86,plain,(
    ! [X6,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | k1_funct_1(X0,sK7(X0,X1,X6)) = X6
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK7(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f244,plain,
    ( spl10_15
    | ~ spl10_11
    | ~ spl10_14 ),
    inference(avatar_split_clause,[],[f239,f229,f203,f242])).

fof(f229,plain,
    ( spl10_14
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | r2_hidden(sK7(sK3,X1,X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f239,plain,
    ( r2_hidden(sK7(sK3,sK2,sK4),sK2)
    | ~ spl10_11
    | ~ spl10_14 ),
    inference(resolution,[],[f230,f204])).

fof(f230,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | r2_hidden(sK7(sK3,X1,X0),X1) )
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f229])).

fof(f234,plain,
    ( ~ spl10_2
    | spl10_13 ),
    inference(avatar_contradiction_clause,[],[f233])).

fof(f233,plain,
    ( $false
    | ~ spl10_2
    | spl10_13 ),
    inference(subsumption_resolution,[],[f100,f232])).

fof(f232,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl10_13 ),
    inference(resolution,[],[f227,f75])).

fof(f227,plain,
    ( ~ v1_relat_1(sK3)
    | spl10_13 ),
    inference(avatar_component_clause,[],[f226])).

fof(f231,plain,
    ( ~ spl10_13
    | spl10_14
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f224,f107,f229,f226])).

fof(f224,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | r2_hidden(sK7(sK3,X1,X0),X1)
        | ~ v1_relat_1(sK3) )
    | ~ spl10_4 ),
    inference(resolution,[],[f87,f108])).

fof(f87,plain,(
    ! [X6,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | r2_hidden(sK7(X0,X1,X6),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f205,plain,
    ( spl10_11
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f195,f99,f95,f203])).

fof(f95,plain,
    ( spl10_1
  <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f195,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(superposition,[],[f96,f191])).

fof(f191,plain,
    ( ! [X0] : k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)
    | ~ spl10_2 ),
    inference(resolution,[],[f83,f100])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f96,plain,
    ( r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f95])).

fof(f115,plain,(
    spl10_5 ),
    inference(avatar_split_clause,[],[f111,f113])).

fof(f111,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f110,f63])).

fof(f63,plain,(
    ! [X0] :
      ( r2_hidden(sK8(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f110,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f70,f53])).

fof(f53,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f109,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f48,f107])).

fof(f48,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f105,plain,(
    spl10_3 ),
    inference(avatar_split_clause,[],[f49,f103])).

fof(f49,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f101,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f50,f99])).

fof(f50,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f31])).

fof(f97,plain,(
    spl10_1 ),
    inference(avatar_split_clause,[],[f51,f95])).

fof(f51,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:19:48 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (19956)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.45  % (19956)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f1445,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f97,f101,f105,f109,f115,f205,f231,f234,f244,f327,f543,f591,f611,f669,f1407,f1432])).
% 0.21/0.45  fof(f1432,plain,(
% 0.21/0.45    ~spl10_15 | ~spl10_11 | ~spl10_18 | ~spl10_62),
% 0.21/0.45    inference(avatar_split_clause,[],[f1138,f667,f325,f203,f242])).
% 0.21/0.45  fof(f242,plain,(
% 0.21/0.45    spl10_15 <=> r2_hidden(sK7(sK3,sK2,sK4),sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).
% 0.21/0.45  fof(f203,plain,(
% 0.21/0.45    spl10_11 <=> r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 0.21/0.45  fof(f325,plain,(
% 0.21/0.45    spl10_18 <=> ! [X1,X0] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | k1_funct_1(sK3,sK7(sK3,X1,X0)) = X0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).
% 0.21/0.45  fof(f667,plain,(
% 0.21/0.45    spl10_62 <=> ! [X5,X4] : (r2_hidden(sK7(sK3,X4,X5),sK0) | ~r2_hidden(X5,k9_relat_1(sK3,X4)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_62])])).
% 0.21/0.45  fof(f1138,plain,(
% 0.21/0.45    ~r2_hidden(sK7(sK3,sK2,sK4),sK2) | (~spl10_11 | ~spl10_18 | ~spl10_62)),
% 0.21/0.45    inference(resolution,[],[f696,f204])).
% 0.21/0.45  fof(f204,plain,(
% 0.21/0.45    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~spl10_11),
% 0.21/0.45    inference(avatar_component_clause,[],[f203])).
% 0.21/0.45  fof(f696,plain,(
% 0.21/0.45    ( ! [X2] : (~r2_hidden(sK4,k9_relat_1(sK3,X2)) | ~r2_hidden(sK7(sK3,X2,sK4),sK2)) ) | (~spl10_18 | ~spl10_62)),
% 0.21/0.45    inference(subsumption_resolution,[],[f332,f668])).
% 0.21/0.45  fof(f668,plain,(
% 0.21/0.45    ( ! [X4,X5] : (r2_hidden(sK7(sK3,X4,X5),sK0) | ~r2_hidden(X5,k9_relat_1(sK3,X4))) ) | ~spl10_62),
% 0.21/0.45    inference(avatar_component_clause,[],[f667])).
% 0.21/0.45  fof(f332,plain,(
% 0.21/0.45    ( ! [X2] : (~r2_hidden(sK7(sK3,X2,sK4),sK0) | ~r2_hidden(sK4,k9_relat_1(sK3,X2)) | ~r2_hidden(sK7(sK3,X2,sK4),sK2)) ) | ~spl10_18),
% 0.21/0.45    inference(resolution,[],[f329,f69])).
% 0.21/0.45  fof(f69,plain,(
% 0.21/0.45    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f21])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.45  fof(f329,plain,(
% 0.21/0.45    ( ! [X0] : (~m1_subset_1(sK7(sK3,X0,sK4),sK0) | ~r2_hidden(sK7(sK3,X0,sK4),sK2) | ~r2_hidden(sK4,k9_relat_1(sK3,X0))) ) | ~spl10_18),
% 0.21/0.45    inference(equality_resolution,[],[f328])).
% 0.21/0.45  fof(f328,plain,(
% 0.21/0.45    ( ! [X0,X1] : (sK4 != X1 | ~r2_hidden(sK7(sK3,X0,X1),sK2) | ~m1_subset_1(sK7(sK3,X0,X1),sK0) | ~r2_hidden(X1,k9_relat_1(sK3,X0))) ) | ~spl10_18),
% 0.21/0.45    inference(superposition,[],[f52,f326])).
% 0.21/0.45  fof(f326,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k1_funct_1(sK3,sK7(sK3,X1,X0)) = X0 | ~r2_hidden(X0,k9_relat_1(sK3,X1))) ) | ~spl10_18),
% 0.21/0.45    inference(avatar_component_clause,[],[f325])).
% 0.21/0.45  fof(f52,plain,(
% 0.21/0.45    ( ! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f31])).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    (! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f16,f30,f29])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ? [X4] : (! [X5] : (k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2))) => (! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.45    inference(flattening,[],[f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.45    inference(ennf_transformation,[],[f14])).
% 0.21/0.45  fof(f14,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.45    inference(negated_conjecture,[],[f13])).
% 0.21/0.45  fof(f13,conjecture,(
% 0.21/0.45    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).
% 0.21/0.45  fof(f1407,plain,(
% 0.21/0.45    ~spl10_5 | ~spl10_11 | ~spl10_51),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f1406])).
% 0.21/0.45  fof(f1406,plain,(
% 0.21/0.45    $false | (~spl10_5 | ~spl10_11 | ~spl10_51)),
% 0.21/0.45    inference(subsumption_resolution,[],[f204,f1401])).
% 0.21/0.45  fof(f1401,plain,(
% 0.21/0.45    ( ! [X12,X13] : (~r2_hidden(X12,k9_relat_1(sK3,X13))) ) | (~spl10_5 | ~spl10_51)),
% 0.21/0.45    inference(subsumption_resolution,[],[f1365,f946])).
% 0.21/0.45  fof(f946,plain,(
% 0.21/0.45    ( ! [X0] : (~r2_hidden(X0,sK3)) ) | (~spl10_5 | ~spl10_51)),
% 0.21/0.45    inference(resolution,[],[f610,f145])).
% 0.21/0.45  fof(f145,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) | ~r2_hidden(X2,X0)) ) | ~spl10_5),
% 0.21/0.45    inference(resolution,[],[f137,f114])).
% 0.21/0.45  fof(f114,plain,(
% 0.21/0.45    v1_xboole_0(k1_xboole_0) | ~spl10_5),
% 0.21/0.45    inference(avatar_component_clause,[],[f113])).
% 0.21/0.45  fof(f113,plain,(
% 0.21/0.45    spl10_5 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.21/0.45  fof(f137,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r2_hidden(X3,X0)) )),
% 0.21/0.45    inference(resolution,[],[f68,f62])).
% 0.21/0.45  fof(f62,plain,(
% 0.21/0.45    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f41])).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK8(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f39,f40])).
% 0.21/0.45  fof(f40,plain,(
% 0.21/0.45    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK8(X0),X0))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.45    inference(rectify,[],[f38])).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.45    inference(nnf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.45  fof(f68,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,axiom,(
% 0.21/0.45    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.21/0.45  fof(f610,plain,(
% 0.21/0.45    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl10_51),
% 0.21/0.45    inference(avatar_component_clause,[],[f609])).
% 0.21/0.45  fof(f609,plain,(
% 0.21/0.45    spl10_51 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_51])])).
% 0.21/0.45  fof(f1365,plain,(
% 0.21/0.45    ( ! [X12,X13] : (r2_hidden(k4_tarski(sK9(X12,X13,sK3),X12),sK3) | ~r2_hidden(X12,k9_relat_1(sK3,X13))) ) | ~spl10_51),
% 0.21/0.45    inference(resolution,[],[f157,f610])).
% 0.21/0.45  fof(f157,plain,(
% 0.21/0.45    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | r2_hidden(k4_tarski(sK9(X0,X2,X1),X0),X1) | ~r2_hidden(X0,k9_relat_1(X1,X2))) )),
% 0.21/0.45    inference(resolution,[],[f72,f75])).
% 0.21/0.45  fof(f75,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f24])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(ennf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.45  fof(f72,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK9(X0,X1,X2),X0),X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f46])).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK9(X0,X1,X2),X0),X2) & r2_hidden(sK9(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f44,f45])).
% 0.21/0.45  fof(f45,plain,(
% 0.21/0.45    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK9(X0,X1,X2),X0),X2) & r2_hidden(sK9(X0,X1,X2),k1_relat_1(X2))))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.45    inference(rectify,[],[f43])).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.45    inference(nnf_transformation,[],[f23])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.45    inference(ennf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 0.21/0.45  fof(f669,plain,(
% 0.21/0.45    ~spl10_13 | ~spl10_4 | spl10_62 | ~spl10_49),
% 0.21/0.45    inference(avatar_split_clause,[],[f637,f588,f667,f107,f226])).
% 0.21/0.45  fof(f226,plain,(
% 0.21/0.45    spl10_13 <=> v1_relat_1(sK3)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 0.21/0.45  fof(f107,plain,(
% 0.21/0.45    spl10_4 <=> v1_funct_1(sK3)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.21/0.45  fof(f588,plain,(
% 0.21/0.45    spl10_49 <=> sK0 = k1_relat_1(sK3)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_49])])).
% 0.21/0.45  fof(f637,plain,(
% 0.21/0.45    ( ! [X4,X5] : (r2_hidden(sK7(sK3,X4,X5),sK0) | ~r2_hidden(X5,k9_relat_1(sK3,X4)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) ) | ~spl10_49),
% 0.21/0.45    inference(superposition,[],[f88,f589])).
% 0.21/0.45  fof(f589,plain,(
% 0.21/0.45    sK0 = k1_relat_1(sK3) | ~spl10_49),
% 0.21/0.45    inference(avatar_component_clause,[],[f588])).
% 0.21/0.45  fof(f88,plain,(
% 0.21/0.45    ( ! [X6,X0,X1] : (r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.45    inference(equality_resolution,[],[f54])).
% 0.21/0.45  fof(f54,plain,(
% 0.21/0.45    ( ! [X6,X2,X0,X1] : (r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f37])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (k1_funct_1(X0,X4) != sK5(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((sK5(X0,X1,X2) = k1_funct_1(X0,sK6(X0,X1,X2)) & r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK7(X0,X1,X6)) = X6 & r2_hidden(sK7(X0,X1,X6),X1) & r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f33,f36,f35,f34])).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((! [X4] : (k1_funct_1(X0,X4) != sK5(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (? [X5] : (k1_funct_1(X0,X5) = sK5(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    ! [X2,X1,X0] : (? [X5] : (k1_funct_1(X0,X5) = sK5(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) => (sK5(X0,X1,X2) = k1_funct_1(X0,sK6(X0,X1,X2)) & r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0))))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f36,plain,(
% 0.21/0.45    ! [X6,X1,X0] : (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) => (k1_funct_1(X0,sK7(X0,X1,X6)) = X6 & r2_hidden(sK7(X0,X1,X6),X1) & r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0))))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.45    inference(rectify,[],[f32])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.45    inference(nnf_transformation,[],[f18])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.45    inference(flattening,[],[f17])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).
% 0.21/0.46  fof(f611,plain,(
% 0.21/0.46    spl10_51 | ~spl10_2 | ~spl10_45),
% 0.21/0.46    inference(avatar_split_clause,[],[f594,f538,f99,f609])).
% 0.21/0.46  fof(f99,plain,(
% 0.21/0.46    spl10_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.21/0.46  fof(f538,plain,(
% 0.21/0.46    spl10_45 <=> k1_xboole_0 = sK1),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl10_45])])).
% 0.21/0.46  fof(f594,plain,(
% 0.21/0.46    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl10_2 | ~spl10_45)),
% 0.21/0.46    inference(superposition,[],[f100,f539])).
% 0.21/0.46  fof(f539,plain,(
% 0.21/0.46    k1_xboole_0 = sK1 | ~spl10_45),
% 0.21/0.46    inference(avatar_component_clause,[],[f538])).
% 0.21/0.46  fof(f100,plain,(
% 0.21/0.46    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl10_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f99])).
% 0.21/0.46  fof(f591,plain,(
% 0.21/0.46    ~spl10_2 | spl10_49 | ~spl10_46),
% 0.21/0.46    inference(avatar_split_clause,[],[f586,f541,f588,f99])).
% 0.21/0.46  fof(f541,plain,(
% 0.21/0.46    spl10_46 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl10_46])])).
% 0.21/0.46  fof(f586,plain,(
% 0.21/0.46    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl10_46),
% 0.21/0.46    inference(superposition,[],[f76,f542])).
% 0.21/0.46  fof(f542,plain,(
% 0.21/0.46    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl10_46),
% 0.21/0.46    inference(avatar_component_clause,[],[f541])).
% 0.21/0.46  fof(f76,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(ennf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.46  fof(f543,plain,(
% 0.21/0.46    ~spl10_2 | spl10_45 | spl10_46 | ~spl10_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f533,f103,f541,f538,f99])).
% 0.21/0.46  fof(f103,plain,(
% 0.21/0.46    spl10_3 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.21/0.46  fof(f533,plain,(
% 0.21/0.46    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl10_3),
% 0.21/0.46    inference(resolution,[],[f77,f104])).
% 0.21/0.46  fof(f104,plain,(
% 0.21/0.46    v1_funct_2(sK3,sK0,sK1) | ~spl10_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f103])).
% 0.21/0.46  fof(f77,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f47])).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(nnf_transformation,[],[f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(flattening,[],[f26])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(ennf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.46  fof(f327,plain,(
% 0.21/0.46    ~spl10_13 | spl10_18 | ~spl10_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f323,f107,f325,f226])).
% 0.21/0.46  fof(f323,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | k1_funct_1(sK3,sK7(sK3,X1,X0)) = X0 | ~v1_relat_1(sK3)) ) | ~spl10_4),
% 0.21/0.46    inference(resolution,[],[f86,f108])).
% 0.21/0.46  fof(f108,plain,(
% 0.21/0.46    v1_funct_1(sK3) | ~spl10_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f107])).
% 0.21/0.46  fof(f86,plain,(
% 0.21/0.46    ( ! [X6,X0,X1] : (~v1_funct_1(X0) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | k1_funct_1(X0,sK7(X0,X1,X6)) = X6 | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(equality_resolution,[],[f56])).
% 0.21/0.46  fof(f56,plain,(
% 0.21/0.46    ( ! [X6,X2,X0,X1] : (k1_funct_1(X0,sK7(X0,X1,X6)) = X6 | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f37])).
% 0.21/0.46  fof(f244,plain,(
% 0.21/0.46    spl10_15 | ~spl10_11 | ~spl10_14),
% 0.21/0.46    inference(avatar_split_clause,[],[f239,f229,f203,f242])).
% 0.21/0.46  fof(f229,plain,(
% 0.21/0.46    spl10_14 <=> ! [X1,X0] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | r2_hidden(sK7(sK3,X1,X0),X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).
% 0.21/0.46  fof(f239,plain,(
% 0.21/0.46    r2_hidden(sK7(sK3,sK2,sK4),sK2) | (~spl10_11 | ~spl10_14)),
% 0.21/0.46    inference(resolution,[],[f230,f204])).
% 0.21/0.46  fof(f230,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | r2_hidden(sK7(sK3,X1,X0),X1)) ) | ~spl10_14),
% 0.21/0.46    inference(avatar_component_clause,[],[f229])).
% 0.21/0.46  fof(f234,plain,(
% 0.21/0.46    ~spl10_2 | spl10_13),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f233])).
% 0.21/0.46  fof(f233,plain,(
% 0.21/0.46    $false | (~spl10_2 | spl10_13)),
% 0.21/0.46    inference(subsumption_resolution,[],[f100,f232])).
% 0.21/0.46  fof(f232,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl10_13),
% 0.21/0.46    inference(resolution,[],[f227,f75])).
% 0.21/0.46  fof(f227,plain,(
% 0.21/0.46    ~v1_relat_1(sK3) | spl10_13),
% 0.21/0.46    inference(avatar_component_clause,[],[f226])).
% 0.21/0.46  fof(f231,plain,(
% 0.21/0.46    ~spl10_13 | spl10_14 | ~spl10_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f224,f107,f229,f226])).
% 0.21/0.46  fof(f224,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | r2_hidden(sK7(sK3,X1,X0),X1) | ~v1_relat_1(sK3)) ) | ~spl10_4),
% 0.21/0.46    inference(resolution,[],[f87,f108])).
% 0.21/0.46  fof(f87,plain,(
% 0.21/0.46    ( ! [X6,X0,X1] : (~v1_funct_1(X0) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | r2_hidden(sK7(X0,X1,X6),X1) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(equality_resolution,[],[f55])).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    ( ! [X6,X2,X0,X1] : (r2_hidden(sK7(X0,X1,X6),X1) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f37])).
% 0.21/0.46  fof(f205,plain,(
% 0.21/0.46    spl10_11 | ~spl10_1 | ~spl10_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f195,f99,f95,f203])).
% 0.21/0.46  fof(f95,plain,(
% 0.21/0.46    spl10_1 <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.21/0.46  fof(f195,plain,(
% 0.21/0.46    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (~spl10_1 | ~spl10_2)),
% 0.21/0.46    inference(superposition,[],[f96,f191])).
% 0.21/0.46  fof(f191,plain,(
% 0.21/0.46    ( ! [X0] : (k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)) ) | ~spl10_2),
% 0.21/0.46    inference(resolution,[],[f83,f100])).
% 0.21/0.46  fof(f83,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f28])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(ennf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.46  fof(f96,plain,(
% 0.21/0.46    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) | ~spl10_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f95])).
% 0.21/0.46  fof(f115,plain,(
% 0.21/0.46    spl10_5),
% 0.21/0.46    inference(avatar_split_clause,[],[f111,f113])).
% 0.21/0.46  fof(f111,plain,(
% 0.21/0.46    v1_xboole_0(k1_xboole_0)),
% 0.21/0.46    inference(resolution,[],[f110,f63])).
% 0.21/0.46  fof(f63,plain,(
% 0.21/0.46    ( ! [X0] : (r2_hidden(sK8(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f41])).
% 0.21/0.46  fof(f110,plain,(
% 0.21/0.46    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.46    inference(resolution,[],[f70,f53])).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.46  fof(f70,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,axiom,(
% 0.21/0.46    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.46  fof(f109,plain,(
% 0.21/0.46    spl10_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f48,f107])).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    v1_funct_1(sK3)),
% 0.21/0.46    inference(cnf_transformation,[],[f31])).
% 0.21/0.46  fof(f105,plain,(
% 0.21/0.46    spl10_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f49,f103])).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f31])).
% 0.21/0.46  fof(f101,plain,(
% 0.21/0.46    spl10_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f50,f99])).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.46    inference(cnf_transformation,[],[f31])).
% 0.21/0.46  fof(f97,plain,(
% 0.21/0.46    spl10_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f51,f95])).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.46    inference(cnf_transformation,[],[f31])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (19956)------------------------------
% 0.21/0.46  % (19956)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (19956)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (19956)Memory used [KB]: 11513
% 0.21/0.46  % (19956)Time elapsed: 0.046 s
% 0.21/0.46  % (19956)------------------------------
% 0.21/0.46  % (19956)------------------------------
% 0.21/0.46  % (19949)Success in time 0.103 s
%------------------------------------------------------------------------------
