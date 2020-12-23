%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 251 expanded)
%              Number of leaves         :   32 ( 113 expanded)
%              Depth                    :   10
%              Number of atoms          :  502 (1307 expanded)
%              Number of equality atoms :   15 (  35 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f279,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f71,f75,f83,f87,f192,f212,f216,f223,f226,f233,f236,f244,f248,f253,f265,f271,f276])).

fof(f276,plain,
    ( ~ spl12_3
    | ~ spl12_4
    | ~ spl12_20 ),
    inference(avatar_split_clause,[],[f272,f269,f73,f69])).

fof(f69,plain,
    ( spl12_3
  <=> r2_hidden(k4_tarski(sK7,sK6),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f73,plain,
    ( spl12_4
  <=> r2_hidden(k4_tarski(sK5,sK7),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

% (25769)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f269,plain,
    ( spl12_20
  <=> ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK6),sK4)
        | ~ r2_hidden(k4_tarski(sK5,X0),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_20])])).

fof(f272,plain,
    ( ~ r2_hidden(k4_tarski(sK7,sK6),sK4)
    | ~ spl12_4
    | ~ spl12_20 ),
    inference(resolution,[],[f270,f74])).

fof(f74,plain,
    ( r2_hidden(k4_tarski(sK5,sK7),sK3)
    | ~ spl12_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f270,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK5,X0),sK3)
        | ~ r2_hidden(k4_tarski(X0,sK6),sK4) )
    | ~ spl12_20 ),
    inference(avatar_component_clause,[],[f269])).

fof(f271,plain,
    ( ~ spl12_12
    | ~ spl12_13
    | spl12_20
    | spl12_11 ),
    inference(avatar_split_clause,[],[f266,f190,f269,f207,f204])).

fof(f204,plain,
    ( spl12_12
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).

fof(f207,plain,
    ( spl12_13
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_13])])).

fof(f190,plain,
    ( spl12_11
  <=> r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).

fof(f266,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK6),sK4)
        | ~ r2_hidden(k4_tarski(sK5,X0),sK3)
        | ~ v1_relat_1(sK4)
        | ~ v1_relat_1(sK3) )
    | spl12_11 ),
    inference(resolution,[],[f264,f90])).

fof(f90,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f57,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f57,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),X2)
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK9(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK8(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK10(X0,X1,X2),sK9(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK8(X0,X1,X2),sK10(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK11(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK11(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11])],[f29,f32,f31,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                | ~ r2_hidden(k4_tarski(X3,X5),X0) )
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ? [X6] :
                ( r2_hidden(k4_tarski(X6,X4),X1)
                & r2_hidden(k4_tarski(X3,X6),X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ! [X5] :
              ( ~ r2_hidden(k4_tarski(X5,sK9(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK8(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK9(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK8(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,sK9(X0,X1,X2)),X1)
          & r2_hidden(k4_tarski(sK8(X0,X1,X2),X6),X0) )
     => ( r2_hidden(k4_tarski(sK10(X0,X1,X2),sK9(X0,X1,X2)),X1)
        & r2_hidden(k4_tarski(sK8(X0,X1,X2),sK10(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK11(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK11(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X6] :
                            ( r2_hidden(k4_tarski(X6,X4),X1)
                            & r2_hidden(k4_tarski(X3,X6),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ? [X10] :
                            ( r2_hidden(k4_tarski(X10,X8),X1)
                            & r2_hidden(k4_tarski(X7,X10),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X3,X4] :
                      ( ( r2_hidden(k4_tarski(X3,X4),X2)
                        | ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) ) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

fof(f264,plain,
    ( ~ r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | spl12_11 ),
    inference(avatar_component_clause,[],[f190])).

fof(f265,plain,
    ( ~ spl12_7
    | ~ spl12_6
    | ~ spl12_11
    | spl12_1 ),
    inference(avatar_split_clause,[],[f263,f61,f190,f81,f85])).

fof(f85,plain,
    ( spl12_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).

fof(f81,plain,
    ( spl12_6
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f61,plain,
    ( spl12_1
  <=> r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f263,plain,
    ( ~ r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl12_1 ),
    inference(superposition,[],[f62,f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(f62,plain,
    ( ~ r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4))
    | spl12_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f253,plain,
    ( ~ spl12_19
    | spl12_18 ),
    inference(avatar_split_clause,[],[f251,f242,f246])).

fof(f246,plain,
    ( spl12_19
  <=> r2_hidden(sK11(sK3,sK4,sK5,sK6),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_19])])).

fof(f242,plain,
    ( spl12_18
  <=> m1_subset_1(sK11(sK3,sK4,sK5,sK6),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_18])])).

fof(f251,plain,
    ( ~ r2_hidden(sK11(sK3,sK4,sK5,sK6),sK1)
    | spl12_18 ),
    inference(resolution,[],[f243,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f243,plain,
    ( ~ m1_subset_1(sK11(sK3,sK4,sK5,sK6),sK1)
    | spl12_18 ),
    inference(avatar_component_clause,[],[f242])).

fof(f248,plain,
    ( spl12_19
    | ~ spl12_6
    | ~ spl12_14 ),
    inference(avatar_split_clause,[],[f238,f210,f81,f246])).

fof(f210,plain,
    ( spl12_14
  <=> r2_hidden(k4_tarski(sK11(sK3,sK4,sK5,sK6),sK6),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_14])])).

fof(f238,plain,
    ( r2_hidden(sK11(sK3,sK4,sK5,sK6),sK1)
    | ~ spl12_6
    | ~ spl12_14 ),
    inference(resolution,[],[f211,f138])).

fof(f138,plain,
    ( ! [X8,X7] :
        ( ~ r2_hidden(k4_tarski(X7,X8),sK4)
        | r2_hidden(X7,sK1) )
    | ~ spl12_6 ),
    inference(resolution,[],[f93,f82])).

fof(f82,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl12_6 ),
    inference(avatar_component_clause,[],[f81])).

fof(f93,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
      | ~ r2_hidden(k4_tarski(X0,X2),X3)
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f53,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f211,plain,
    ( r2_hidden(k4_tarski(sK11(sK3,sK4,sK5,sK6),sK6),sK4)
    | ~ spl12_14 ),
    inference(avatar_component_clause,[],[f210])).

fof(f244,plain,
    ( ~ spl12_15
    | ~ spl12_18
    | ~ spl12_2
    | ~ spl12_14 ),
    inference(avatar_split_clause,[],[f237,f210,f64,f242,f214])).

fof(f214,plain,
    ( spl12_15
  <=> r2_hidden(k4_tarski(sK5,sK11(sK3,sK4,sK5,sK6)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_15])])).

fof(f64,plain,
    ( spl12_2
  <=> ! [X7] :
        ( ~ r2_hidden(k4_tarski(X7,sK6),sK4)
        | ~ m1_subset_1(X7,sK1)
        | ~ r2_hidden(k4_tarski(sK5,X7),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f237,plain,
    ( ~ m1_subset_1(sK11(sK3,sK4,sK5,sK6),sK1)
    | ~ r2_hidden(k4_tarski(sK5,sK11(sK3,sK4,sK5,sK6)),sK3)
    | ~ spl12_2
    | ~ spl12_14 ),
    inference(resolution,[],[f211,f65])).

fof(f65,plain,
    ( ! [X7] :
        ( ~ r2_hidden(k4_tarski(X7,sK6),sK4)
        | ~ m1_subset_1(X7,sK1)
        | ~ r2_hidden(k4_tarski(sK5,X7),sK3) )
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f236,plain,(
    spl12_17 ),
    inference(avatar_contradiction_clause,[],[f234])).

fof(f234,plain,
    ( $false
    | spl12_17 ),
    inference(resolution,[],[f232,f49])).

fof(f49,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f232,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | spl12_17 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl12_17
  <=> v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_17])])).

fof(f233,plain,
    ( ~ spl12_17
    | ~ spl12_6
    | spl12_13 ),
    inference(avatar_split_clause,[],[f228,f207,f81,f231])).

fof(f228,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | ~ spl12_6
    | spl12_13 ),
    inference(resolution,[],[f227,f82])).

fof(f227,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl12_13 ),
    inference(resolution,[],[f208,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f208,plain,
    ( ~ v1_relat_1(sK4)
    | spl12_13 ),
    inference(avatar_component_clause,[],[f207])).

fof(f226,plain,(
    spl12_16 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | spl12_16 ),
    inference(resolution,[],[f222,f49])).

fof(f222,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl12_16 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl12_16
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_16])])).

fof(f223,plain,
    ( ~ spl12_16
    | ~ spl12_7
    | spl12_12 ),
    inference(avatar_split_clause,[],[f218,f204,f85,f221])).

fof(f218,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl12_7
    | spl12_12 ),
    inference(resolution,[],[f217,f86])).

fof(f86,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl12_7 ),
    inference(avatar_component_clause,[],[f85])).

fof(f217,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl12_12 ),
    inference(resolution,[],[f205,f48])).

fof(f205,plain,
    ( ~ v1_relat_1(sK3)
    | spl12_12 ),
    inference(avatar_component_clause,[],[f204])).

fof(f216,plain,
    ( ~ spl12_12
    | ~ spl12_13
    | spl12_15
    | ~ spl12_11 ),
    inference(avatar_split_clause,[],[f201,f190,f214,f207,f204])).

fof(f201,plain,
    ( r2_hidden(k4_tarski(sK5,sK11(sK3,sK4,sK5,sK6)),sK3)
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK3)
    | ~ spl12_11 ),
    inference(resolution,[],[f191,f88])).

fof(f88,plain,(
    ! [X0,X8,X7,X1] :
      ( ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X7,sK11(X0,X1,X7,X8)),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f59,f52])).

fof(f59,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK11(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK11(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f191,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | ~ spl12_11 ),
    inference(avatar_component_clause,[],[f190])).

fof(f212,plain,
    ( ~ spl12_12
    | ~ spl12_13
    | spl12_14
    | ~ spl12_11 ),
    inference(avatar_split_clause,[],[f200,f190,f210,f207,f204])).

fof(f200,plain,
    ( r2_hidden(k4_tarski(sK11(sK3,sK4,sK5,sK6),sK6),sK4)
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK3)
    | ~ spl12_11 ),
    inference(resolution,[],[f191,f89])).

fof(f89,plain,(
    ! [X0,X8,X7,X1] :
      ( ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(sK11(X0,X1,X7,X8),X8),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f58,f52])).

fof(f58,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK11(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK11(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f192,plain,
    ( ~ spl12_7
    | ~ spl12_6
    | spl12_11
    | ~ spl12_1 ),
    inference(avatar_split_clause,[],[f182,f61,f190,f81,f85])).

fof(f182,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl12_1 ),
    inference(superposition,[],[f67,f56])).

fof(f67,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4))
    | ~ spl12_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f87,plain,(
    spl12_7 ),
    inference(avatar_split_clause,[],[f36,f85])).

fof(f36,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( ! [X7] :
          ( ~ r2_hidden(k4_tarski(X7,sK6),sK4)
          | ~ r2_hidden(k4_tarski(sK5,X7),sK3)
          | ~ m1_subset_1(X7,sK1) )
      | ~ r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) )
    & ( ( r2_hidden(k4_tarski(sK7,sK6),sK4)
        & r2_hidden(k4_tarski(sK5,sK7),sK3)
        & m1_subset_1(sK7,sK1) )
      | r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f22,f26,f25,f24,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ? [X5,X6] :
                ( ( ! [X7] :
                      ( ~ r2_hidden(k4_tarski(X7,X6),X4)
                      | ~ r2_hidden(k4_tarski(X5,X7),X3)
                      | ~ m1_subset_1(X7,X1) )
                  | ~ r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) )
                & ( ? [X8] :
                      ( r2_hidden(k4_tarski(X8,X6),X4)
                      & r2_hidden(k4_tarski(X5,X8),X3)
                      & m1_subset_1(X8,X1) )
                  | r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) ) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ? [X4] :
          ( ? [X6,X5] :
              ( ( ! [X7] :
                    ( ~ r2_hidden(k4_tarski(X7,X6),X4)
                    | ~ r2_hidden(k4_tarski(X5,X7),sK3)
                    | ~ m1_subset_1(X7,sK1) )
                | ~ r2_hidden(k4_tarski(X5,X6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,X4)) )
              & ( ? [X8] :
                    ( r2_hidden(k4_tarski(X8,X6),X4)
                    & r2_hidden(k4_tarski(X5,X8),sK3)
                    & m1_subset_1(X8,sK1) )
                | r2_hidden(k4_tarski(X5,X6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,X4)) ) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X4] :
        ( ? [X6,X5] :
            ( ( ! [X7] :
                  ( ~ r2_hidden(k4_tarski(X7,X6),X4)
                  | ~ r2_hidden(k4_tarski(X5,X7),sK3)
                  | ~ m1_subset_1(X7,sK1) )
              | ~ r2_hidden(k4_tarski(X5,X6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,X4)) )
            & ( ? [X8] :
                  ( r2_hidden(k4_tarski(X8,X6),X4)
                  & r2_hidden(k4_tarski(X5,X8),sK3)
                  & m1_subset_1(X8,sK1) )
              | r2_hidden(k4_tarski(X5,X6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,X4)) ) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) )
   => ( ? [X6,X5] :
          ( ( ! [X7] :
                ( ~ r2_hidden(k4_tarski(X7,X6),sK4)
                | ~ r2_hidden(k4_tarski(X5,X7),sK3)
                | ~ m1_subset_1(X7,sK1) )
            | ~ r2_hidden(k4_tarski(X5,X6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) )
          & ( ? [X8] :
                ( r2_hidden(k4_tarski(X8,X6),sK4)
                & r2_hidden(k4_tarski(X5,X8),sK3)
                & m1_subset_1(X8,sK1) )
            | r2_hidden(k4_tarski(X5,X6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) ) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X6,X5] :
        ( ( ! [X7] :
              ( ~ r2_hidden(k4_tarski(X7,X6),sK4)
              | ~ r2_hidden(k4_tarski(X5,X7),sK3)
              | ~ m1_subset_1(X7,sK1) )
          | ~ r2_hidden(k4_tarski(X5,X6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) )
        & ( ? [X8] :
              ( r2_hidden(k4_tarski(X8,X6),sK4)
              & r2_hidden(k4_tarski(X5,X8),sK3)
              & m1_subset_1(X8,sK1) )
          | r2_hidden(k4_tarski(X5,X6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) ) )
   => ( ( ! [X7] :
            ( ~ r2_hidden(k4_tarski(X7,sK6),sK4)
            | ~ r2_hidden(k4_tarski(sK5,X7),sK3)
            | ~ m1_subset_1(X7,sK1) )
        | ~ r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) )
      & ( ? [X8] :
            ( r2_hidden(k4_tarski(X8,sK6),sK4)
            & r2_hidden(k4_tarski(sK5,X8),sK3)
            & m1_subset_1(X8,sK1) )
        | r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X8] :
        ( r2_hidden(k4_tarski(X8,sK6),sK4)
        & r2_hidden(k4_tarski(sK5,X8),sK3)
        & m1_subset_1(X8,sK1) )
   => ( r2_hidden(k4_tarski(sK7,sK6),sK4)
      & r2_hidden(k4_tarski(sK5,sK7),sK3)
      & m1_subset_1(sK7,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5,X6] :
              ( ( ! [X7] :
                    ( ~ r2_hidden(k4_tarski(X7,X6),X4)
                    | ~ r2_hidden(k4_tarski(X5,X7),X3)
                    | ~ m1_subset_1(X7,X1) )
                | ~ r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) )
              & ( ? [X8] :
                    ( r2_hidden(k4_tarski(X8,X6),X4)
                    & r2_hidden(k4_tarski(X5,X8),X3)
                    & m1_subset_1(X8,X1) )
                | r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) ) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5,X6] :
              ( ( ! [X7] :
                    ( ~ r2_hidden(k4_tarski(X7,X6),X4)
                    | ~ r2_hidden(k4_tarski(X5,X7),X3)
                    | ~ m1_subset_1(X7,X1) )
                | ~ r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) )
              & ( ? [X7] :
                    ( r2_hidden(k4_tarski(X7,X6),X4)
                    & r2_hidden(k4_tarski(X5,X7),X3)
                    & m1_subset_1(X7,X1) )
                | r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) ) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5,X6] :
              ( r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4))
            <~> ? [X7] :
                  ( r2_hidden(k4_tarski(X7,X6),X4)
                  & r2_hidden(k4_tarski(X5,X7),X3)
                  & m1_subset_1(X7,X1) ) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ! [X4] :
            ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
           => ! [X5,X6] :
                ( r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4))
              <=> ? [X7] :
                    ( r2_hidden(k4_tarski(X7,X6),X4)
                    & r2_hidden(k4_tarski(X5,X7),X3)
                    & m1_subset_1(X7,X1) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ~ v1_xboole_0(X2)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                       => ! [X5,X6] :
                            ( r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4))
                          <=> ? [X7] :
                                ( r2_hidden(k4_tarski(X7,X6),X4)
                                & r2_hidden(k4_tarski(X5,X7),X3)
                                & m1_subset_1(X7,X1) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                     => ! [X5,X6] :
                          ( r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4))
                        <=> ? [X7] :
                              ( r2_hidden(k4_tarski(X7,X6),X4)
                              & r2_hidden(k4_tarski(X5,X7),X3)
                              & m1_subset_1(X7,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_relset_1)).

fof(f83,plain,(
    spl12_6 ),
    inference(avatar_split_clause,[],[f37,f81])).

fof(f37,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f27])).

fof(f75,plain,
    ( spl12_1
    | spl12_4 ),
    inference(avatar_split_clause,[],[f39,f73,f61])).

fof(f39,plain,
    ( r2_hidden(k4_tarski(sK5,sK7),sK3)
    | r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f27])).

fof(f71,plain,
    ( spl12_1
    | spl12_3 ),
    inference(avatar_split_clause,[],[f40,f69,f61])).

fof(f40,plain,
    ( r2_hidden(k4_tarski(sK7,sK6),sK4)
    | r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f27])).

fof(f66,plain,
    ( ~ spl12_1
    | spl12_2 ),
    inference(avatar_split_clause,[],[f41,f64,f61])).

fof(f41,plain,(
    ! [X7] :
      ( ~ r2_hidden(k4_tarski(X7,sK6),sK4)
      | ~ r2_hidden(k4_tarski(sK5,X7),sK3)
      | ~ m1_subset_1(X7,sK1)
      | ~ r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) ) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:13:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (25759)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.47  % (25753)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.47  % (25764)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % (25756)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.48  % (25766)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.48  % (25761)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.50  % (25754)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.50  % (25756)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f279,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f66,f71,f75,f83,f87,f192,f212,f216,f223,f226,f233,f236,f244,f248,f253,f265,f271,f276])).
% 0.20/0.50  fof(f276,plain,(
% 0.20/0.50    ~spl12_3 | ~spl12_4 | ~spl12_20),
% 0.20/0.50    inference(avatar_split_clause,[],[f272,f269,f73,f69])).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    spl12_3 <=> r2_hidden(k4_tarski(sK7,sK6),sK4)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    spl12_4 <=> r2_hidden(k4_tarski(sK5,sK7),sK3)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).
% 0.20/0.50  % (25769)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.50  fof(f269,plain,(
% 0.20/0.50    spl12_20 <=> ! [X0] : (~r2_hidden(k4_tarski(X0,sK6),sK4) | ~r2_hidden(k4_tarski(sK5,X0),sK3))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl12_20])])).
% 0.20/0.50  fof(f272,plain,(
% 0.20/0.50    ~r2_hidden(k4_tarski(sK7,sK6),sK4) | (~spl12_4 | ~spl12_20)),
% 0.20/0.50    inference(resolution,[],[f270,f74])).
% 0.20/0.50  fof(f74,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK5,sK7),sK3) | ~spl12_4),
% 0.20/0.50    inference(avatar_component_clause,[],[f73])).
% 0.20/0.50  fof(f270,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(k4_tarski(sK5,X0),sK3) | ~r2_hidden(k4_tarski(X0,sK6),sK4)) ) | ~spl12_20),
% 0.20/0.50    inference(avatar_component_clause,[],[f269])).
% 0.20/0.50  fof(f271,plain,(
% 0.20/0.50    ~spl12_12 | ~spl12_13 | spl12_20 | spl12_11),
% 0.20/0.50    inference(avatar_split_clause,[],[f266,f190,f269,f207,f204])).
% 0.20/0.50  fof(f204,plain,(
% 0.20/0.50    spl12_12 <=> v1_relat_1(sK3)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).
% 0.20/0.50  fof(f207,plain,(
% 0.20/0.50    spl12_13 <=> v1_relat_1(sK4)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl12_13])])).
% 0.20/0.50  fof(f190,plain,(
% 0.20/0.50    spl12_11 <=> r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).
% 0.20/0.50  fof(f266,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK6),sK4) | ~r2_hidden(k4_tarski(sK5,X0),sK3) | ~v1_relat_1(sK4) | ~v1_relat_1(sK3)) ) | spl12_11),
% 0.20/0.50    inference(resolution,[],[f264,f90])).
% 0.20/0.50  fof(f90,plain,(
% 0.20/0.50    ( ! [X0,X8,X7,X1,X9] : (r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f57,f52])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ( ! [X0,X8,X7,X1,X9] : (r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ( ! [X2,X0,X8,X7,X1,X9] : (r2_hidden(k4_tarski(X7,X8),X2) | ~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ((! [X5] : (~r2_hidden(k4_tarski(X5,sK9(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK8(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK10(X0,X1,X2),sK9(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK8(X0,X1,X2),sK10(X0,X1,X2)),X0)) | r2_hidden(k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & ((r2_hidden(k4_tarski(sK11(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK11(X0,X1,X7,X8)),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11])],[f29,f32,f31,f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X2,X1,X0] : (? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((! [X5] : (~r2_hidden(k4_tarski(X5,sK9(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK8(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,sK9(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK8(X0,X1,X2),X6),X0)) | r2_hidden(k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)),X2))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ! [X2,X1,X0] : (? [X6] : (r2_hidden(k4_tarski(X6,sK9(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK8(X0,X1,X2),X6),X0)) => (r2_hidden(k4_tarski(sK10(X0,X1,X2),sK9(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK8(X0,X1,X2),sK10(X0,X1,X2)),X0)))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ! [X8,X7,X1,X0] : (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) => (r2_hidden(k4_tarski(sK11(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK11(X0,X1,X7,X8)),X0)))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(rectify,[],[f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(nnf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).
% 0.20/0.50  fof(f264,plain,(
% 0.20/0.50    ~r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4)) | spl12_11),
% 0.20/0.50    inference(avatar_component_clause,[],[f190])).
% 0.20/0.50  fof(f265,plain,(
% 0.20/0.50    ~spl12_7 | ~spl12_6 | ~spl12_11 | spl12_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f263,f61,f190,f81,f85])).
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    spl12_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).
% 0.20/0.50  fof(f81,plain,(
% 0.20/0.50    spl12_6 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    spl12_1 <=> r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
% 0.20/0.50  fof(f263,plain,(
% 0.20/0.50    ~r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl12_1),
% 0.20/0.50    inference(superposition,[],[f62,f56])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(flattening,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    ~r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) | spl12_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f61])).
% 0.20/0.50  fof(f253,plain,(
% 0.20/0.50    ~spl12_19 | spl12_18),
% 0.20/0.50    inference(avatar_split_clause,[],[f251,f242,f246])).
% 0.20/0.50  fof(f246,plain,(
% 0.20/0.50    spl12_19 <=> r2_hidden(sK11(sK3,sK4,sK5,sK6),sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl12_19])])).
% 0.20/0.50  fof(f242,plain,(
% 0.20/0.50    spl12_18 <=> m1_subset_1(sK11(sK3,sK4,sK5,sK6),sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl12_18])])).
% 0.20/0.50  fof(f251,plain,(
% 0.20/0.50    ~r2_hidden(sK11(sK3,sK4,sK5,sK6),sK1) | spl12_18),
% 0.20/0.50    inference(resolution,[],[f243,f50])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.20/0.50  fof(f243,plain,(
% 0.20/0.50    ~m1_subset_1(sK11(sK3,sK4,sK5,sK6),sK1) | spl12_18),
% 0.20/0.50    inference(avatar_component_clause,[],[f242])).
% 0.20/0.50  fof(f248,plain,(
% 0.20/0.50    spl12_19 | ~spl12_6 | ~spl12_14),
% 0.20/0.50    inference(avatar_split_clause,[],[f238,f210,f81,f246])).
% 0.20/0.50  fof(f210,plain,(
% 0.20/0.50    spl12_14 <=> r2_hidden(k4_tarski(sK11(sK3,sK4,sK5,sK6),sK6),sK4)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl12_14])])).
% 0.20/0.50  fof(f238,plain,(
% 0.20/0.50    r2_hidden(sK11(sK3,sK4,sK5,sK6),sK1) | (~spl12_6 | ~spl12_14)),
% 0.20/0.50    inference(resolution,[],[f211,f138])).
% 0.20/0.50  fof(f138,plain,(
% 0.20/0.50    ( ! [X8,X7] : (~r2_hidden(k4_tarski(X7,X8),sK4) | r2_hidden(X7,sK1)) ) | ~spl12_6),
% 0.20/0.50    inference(resolution,[],[f93,f82])).
% 0.20/0.50  fof(f82,plain,(
% 0.20/0.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl12_6),
% 0.20/0.50    inference(avatar_component_clause,[],[f81])).
% 0.20/0.50  fof(f93,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X4))) | ~r2_hidden(k4_tarski(X0,X2),X3) | r2_hidden(X0,X1)) )),
% 0.20/0.50    inference(resolution,[],[f53,f51])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.20/0.50    inference(flattening,[],[f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.20/0.50    inference(nnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.20/0.50  fof(f211,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK11(sK3,sK4,sK5,sK6),sK6),sK4) | ~spl12_14),
% 0.20/0.50    inference(avatar_component_clause,[],[f210])).
% 0.20/0.50  fof(f244,plain,(
% 0.20/0.50    ~spl12_15 | ~spl12_18 | ~spl12_2 | ~spl12_14),
% 0.20/0.50    inference(avatar_split_clause,[],[f237,f210,f64,f242,f214])).
% 0.20/0.50  fof(f214,plain,(
% 0.20/0.50    spl12_15 <=> r2_hidden(k4_tarski(sK5,sK11(sK3,sK4,sK5,sK6)),sK3)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl12_15])])).
% 0.20/0.50  fof(f64,plain,(
% 0.20/0.50    spl12_2 <=> ! [X7] : (~r2_hidden(k4_tarski(X7,sK6),sK4) | ~m1_subset_1(X7,sK1) | ~r2_hidden(k4_tarski(sK5,X7),sK3))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).
% 0.20/0.50  fof(f237,plain,(
% 0.20/0.50    ~m1_subset_1(sK11(sK3,sK4,sK5,sK6),sK1) | ~r2_hidden(k4_tarski(sK5,sK11(sK3,sK4,sK5,sK6)),sK3) | (~spl12_2 | ~spl12_14)),
% 0.20/0.50    inference(resolution,[],[f211,f65])).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    ( ! [X7] : (~r2_hidden(k4_tarski(X7,sK6),sK4) | ~m1_subset_1(X7,sK1) | ~r2_hidden(k4_tarski(sK5,X7),sK3)) ) | ~spl12_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f64])).
% 0.20/0.50  fof(f236,plain,(
% 0.20/0.50    spl12_17),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f234])).
% 0.20/0.50  fof(f234,plain,(
% 0.20/0.50    $false | spl12_17),
% 0.20/0.50    inference(resolution,[],[f232,f49])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.50  fof(f232,plain,(
% 0.20/0.50    ~v1_relat_1(k2_zfmisc_1(sK1,sK2)) | spl12_17),
% 0.20/0.50    inference(avatar_component_clause,[],[f231])).
% 0.20/0.50  fof(f231,plain,(
% 0.20/0.50    spl12_17 <=> v1_relat_1(k2_zfmisc_1(sK1,sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl12_17])])).
% 0.20/0.50  fof(f233,plain,(
% 0.20/0.50    ~spl12_17 | ~spl12_6 | spl12_13),
% 0.20/0.50    inference(avatar_split_clause,[],[f228,f207,f81,f231])).
% 0.20/0.50  fof(f228,plain,(
% 0.20/0.50    ~v1_relat_1(k2_zfmisc_1(sK1,sK2)) | (~spl12_6 | spl12_13)),
% 0.20/0.50    inference(resolution,[],[f227,f82])).
% 0.20/0.50  fof(f227,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl12_13),
% 0.20/0.50    inference(resolution,[],[f208,f48])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.50  fof(f208,plain,(
% 0.20/0.50    ~v1_relat_1(sK4) | spl12_13),
% 0.20/0.50    inference(avatar_component_clause,[],[f207])).
% 0.20/0.50  fof(f226,plain,(
% 0.20/0.50    spl12_16),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f224])).
% 0.20/0.50  fof(f224,plain,(
% 0.20/0.50    $false | spl12_16),
% 0.20/0.50    inference(resolution,[],[f222,f49])).
% 0.20/0.50  fof(f222,plain,(
% 0.20/0.50    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl12_16),
% 0.20/0.50    inference(avatar_component_clause,[],[f221])).
% 0.20/0.50  fof(f221,plain,(
% 0.20/0.50    spl12_16 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl12_16])])).
% 0.20/0.50  fof(f223,plain,(
% 0.20/0.50    ~spl12_16 | ~spl12_7 | spl12_12),
% 0.20/0.50    inference(avatar_split_clause,[],[f218,f204,f85,f221])).
% 0.20/0.50  fof(f218,plain,(
% 0.20/0.50    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | (~spl12_7 | spl12_12)),
% 0.20/0.50    inference(resolution,[],[f217,f86])).
% 0.20/0.50  fof(f86,plain,(
% 0.20/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl12_7),
% 0.20/0.50    inference(avatar_component_clause,[],[f85])).
% 0.20/0.50  fof(f217,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl12_12),
% 0.20/0.50    inference(resolution,[],[f205,f48])).
% 0.20/0.50  fof(f205,plain,(
% 0.20/0.50    ~v1_relat_1(sK3) | spl12_12),
% 0.20/0.50    inference(avatar_component_clause,[],[f204])).
% 0.20/0.50  fof(f216,plain,(
% 0.20/0.50    ~spl12_12 | ~spl12_13 | spl12_15 | ~spl12_11),
% 0.20/0.50    inference(avatar_split_clause,[],[f201,f190,f214,f207,f204])).
% 0.20/0.50  fof(f201,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK5,sK11(sK3,sK4,sK5,sK6)),sK3) | ~v1_relat_1(sK4) | ~v1_relat_1(sK3) | ~spl12_11),
% 0.20/0.50    inference(resolution,[],[f191,f88])).
% 0.20/0.50  fof(f88,plain,(
% 0.20/0.50    ( ! [X0,X8,X7,X1] : (~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | r2_hidden(k4_tarski(X7,sK11(X0,X1,X7,X8)),X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f59,f52])).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK11(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK11(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f33])).
% 0.20/0.50  fof(f191,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4)) | ~spl12_11),
% 0.20/0.50    inference(avatar_component_clause,[],[f190])).
% 0.20/0.50  fof(f212,plain,(
% 0.20/0.50    ~spl12_12 | ~spl12_13 | spl12_14 | ~spl12_11),
% 0.20/0.50    inference(avatar_split_clause,[],[f200,f190,f210,f207,f204])).
% 0.20/0.50  fof(f200,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK11(sK3,sK4,sK5,sK6),sK6),sK4) | ~v1_relat_1(sK4) | ~v1_relat_1(sK3) | ~spl12_11),
% 0.20/0.50    inference(resolution,[],[f191,f89])).
% 0.20/0.50  fof(f89,plain,(
% 0.20/0.50    ( ! [X0,X8,X7,X1] : (~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | r2_hidden(k4_tarski(sK11(X0,X1,X7,X8),X8),X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f58,f52])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK11(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK11(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f33])).
% 0.20/0.50  fof(f192,plain,(
% 0.20/0.50    ~spl12_7 | ~spl12_6 | spl12_11 | ~spl12_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f182,f61,f190,f81,f85])).
% 0.20/0.50  fof(f182,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl12_1),
% 0.20/0.50    inference(superposition,[],[f67,f56])).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) | ~spl12_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f61])).
% 0.20/0.50  fof(f87,plain,(
% 0.20/0.50    spl12_7),
% 0.20/0.50    inference(avatar_split_clause,[],[f36,f85])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.50    inference(cnf_transformation,[],[f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    (((! [X7] : (~r2_hidden(k4_tarski(X7,sK6),sK4) | ~r2_hidden(k4_tarski(sK5,X7),sK3) | ~m1_subset_1(X7,sK1)) | ~r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4))) & ((r2_hidden(k4_tarski(sK7,sK6),sK4) & r2_hidden(k4_tarski(sK5,sK7),sK3) & m1_subset_1(sK7,sK1)) | r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f22,f26,f25,f24,f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ? [X0,X1,X2,X3] : (? [X4] : (? [X5,X6] : ((! [X7] : (~r2_hidden(k4_tarski(X7,X6),X4) | ~r2_hidden(k4_tarski(X5,X7),X3) | ~m1_subset_1(X7,X1)) | ~r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4))) & (? [X8] : (r2_hidden(k4_tarski(X8,X6),X4) & r2_hidden(k4_tarski(X5,X8),X3) & m1_subset_1(X8,X1)) | r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (? [X4] : (? [X6,X5] : ((! [X7] : (~r2_hidden(k4_tarski(X7,X6),X4) | ~r2_hidden(k4_tarski(X5,X7),sK3) | ~m1_subset_1(X7,sK1)) | ~r2_hidden(k4_tarski(X5,X6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,X4))) & (? [X8] : (r2_hidden(k4_tarski(X8,X6),X4) & r2_hidden(k4_tarski(X5,X8),sK3) & m1_subset_1(X8,sK1)) | r2_hidden(k4_tarski(X5,X6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,X4)))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ? [X4] : (? [X6,X5] : ((! [X7] : (~r2_hidden(k4_tarski(X7,X6),X4) | ~r2_hidden(k4_tarski(X5,X7),sK3) | ~m1_subset_1(X7,sK1)) | ~r2_hidden(k4_tarski(X5,X6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,X4))) & (? [X8] : (r2_hidden(k4_tarski(X8,X6),X4) & r2_hidden(k4_tarski(X5,X8),sK3) & m1_subset_1(X8,sK1)) | r2_hidden(k4_tarski(X5,X6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,X4)))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))) => (? [X6,X5] : ((! [X7] : (~r2_hidden(k4_tarski(X7,X6),sK4) | ~r2_hidden(k4_tarski(X5,X7),sK3) | ~m1_subset_1(X7,sK1)) | ~r2_hidden(k4_tarski(X5,X6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4))) & (? [X8] : (r2_hidden(k4_tarski(X8,X6),sK4) & r2_hidden(k4_tarski(X5,X8),sK3) & m1_subset_1(X8,sK1)) | r2_hidden(k4_tarski(X5,X6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ? [X6,X5] : ((! [X7] : (~r2_hidden(k4_tarski(X7,X6),sK4) | ~r2_hidden(k4_tarski(X5,X7),sK3) | ~m1_subset_1(X7,sK1)) | ~r2_hidden(k4_tarski(X5,X6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4))) & (? [X8] : (r2_hidden(k4_tarski(X8,X6),sK4) & r2_hidden(k4_tarski(X5,X8),sK3) & m1_subset_1(X8,sK1)) | r2_hidden(k4_tarski(X5,X6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)))) => ((! [X7] : (~r2_hidden(k4_tarski(X7,sK6),sK4) | ~r2_hidden(k4_tarski(sK5,X7),sK3) | ~m1_subset_1(X7,sK1)) | ~r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4))) & (? [X8] : (r2_hidden(k4_tarski(X8,sK6),sK4) & r2_hidden(k4_tarski(sK5,X8),sK3) & m1_subset_1(X8,sK1)) | r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ? [X8] : (r2_hidden(k4_tarski(X8,sK6),sK4) & r2_hidden(k4_tarski(sK5,X8),sK3) & m1_subset_1(X8,sK1)) => (r2_hidden(k4_tarski(sK7,sK6),sK4) & r2_hidden(k4_tarski(sK5,sK7),sK3) & m1_subset_1(sK7,sK1))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ? [X0,X1,X2,X3] : (? [X4] : (? [X5,X6] : ((! [X7] : (~r2_hidden(k4_tarski(X7,X6),X4) | ~r2_hidden(k4_tarski(X5,X7),X3) | ~m1_subset_1(X7,X1)) | ~r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4))) & (? [X8] : (r2_hidden(k4_tarski(X8,X6),X4) & r2_hidden(k4_tarski(X5,X8),X3) & m1_subset_1(X8,X1)) | r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(rectify,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ? [X0,X1,X2,X3] : (? [X4] : (? [X5,X6] : ((! [X7] : (~r2_hidden(k4_tarski(X7,X6),X4) | ~r2_hidden(k4_tarski(X5,X7),X3) | ~m1_subset_1(X7,X1)) | ~r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4))) & (? [X7] : (r2_hidden(k4_tarski(X7,X6),X4) & r2_hidden(k4_tarski(X5,X7),X3) & m1_subset_1(X7,X1)) | r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(nnf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ? [X0,X1,X2,X3] : (? [X4] : (? [X5,X6] : (r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) <~> ? [X7] : (r2_hidden(k4_tarski(X7,X6),X4) & r2_hidden(k4_tarski(X5,X7),X3) & m1_subset_1(X7,X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ! [X5,X6] : (r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) <=> ? [X7] : (r2_hidden(k4_tarski(X7,X6),X4) & r2_hidden(k4_tarski(X5,X7),X3) & m1_subset_1(X7,X1)))))),
% 0.20/0.50    inference(pure_predicate_removal,[],[f10])).
% 0.20/0.50  fof(f10,negated_conjecture,(
% 0.20/0.50    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ! [X5,X6] : (r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) <=> ? [X7] : (r2_hidden(k4_tarski(X7,X6),X4) & r2_hidden(k4_tarski(X5,X7),X3) & m1_subset_1(X7,X1))))))))),
% 0.20/0.50    inference(negated_conjecture,[],[f9])).
% 0.20/0.50  fof(f9,conjecture,(
% 0.20/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ! [X5,X6] : (r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) <=> ? [X7] : (r2_hidden(k4_tarski(X7,X6),X4) & r2_hidden(k4_tarski(X5,X7),X3) & m1_subset_1(X7,X1))))))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_relset_1)).
% 0.20/0.50  fof(f83,plain,(
% 0.20/0.50    spl12_6),
% 0.20/0.50    inference(avatar_split_clause,[],[f37,f81])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.50    inference(cnf_transformation,[],[f27])).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    spl12_1 | spl12_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f39,f73,f61])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK5,sK7),sK3) | r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4))),
% 0.20/0.50    inference(cnf_transformation,[],[f27])).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    spl12_1 | spl12_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f40,f69,f61])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK7,sK6),sK4) | r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4))),
% 0.20/0.50    inference(cnf_transformation,[],[f27])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    ~spl12_1 | spl12_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f41,f64,f61])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ( ! [X7] : (~r2_hidden(k4_tarski(X7,sK6),sK4) | ~r2_hidden(k4_tarski(sK5,X7),sK3) | ~m1_subset_1(X7,sK1) | ~r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f27])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (25756)------------------------------
% 0.20/0.50  % (25756)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (25756)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (25756)Memory used [KB]: 10874
% 0.20/0.50  % (25756)Time elapsed: 0.025 s
% 0.20/0.50  % (25756)------------------------------
% 0.20/0.50  % (25756)------------------------------
% 0.20/0.50  % (25767)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.50  % (25745)Success in time 0.147 s
%------------------------------------------------------------------------------
