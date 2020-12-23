%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 246 expanded)
%              Number of leaves         :   37 ( 111 expanded)
%              Depth                    :   13
%              Number of atoms          :  469 (1117 expanded)
%              Number of equality atoms :   64 (  86 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f334,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f82,f86,f90,f94,f98,f102,f107,f118,f129,f158,f165,f197,f200,f205,f206,f213,f220,f260,f327,f333])).

fof(f333,plain,
    ( ~ spl5_27
    | spl5_12
    | ~ spl5_41 ),
    inference(avatar_split_clause,[],[f331,f325,f127,f231])).

fof(f231,plain,
    ( spl5_27
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f127,plain,
    ( spl5_12
  <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f325,plain,
    ( spl5_41
  <=> k2_relat_1(sK3) = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f331,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl5_41 ),
    inference(superposition,[],[f50,f326])).

fof(f326,plain,
    ( k2_relat_1(sK3) = k2_relset_1(sK1,sK0,sK3)
    | ~ spl5_41 ),
    inference(avatar_component_clause,[],[f325])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f327,plain,
    ( spl5_41
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f323,f231,f325])).

fof(f323,plain,
    ( k2_relat_1(sK3) = k2_relset_1(sK1,sK0,sK3)
    | ~ spl5_27 ),
    inference(resolution,[],[f232,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f232,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f231])).

fof(f260,plain,
    ( spl5_27
    | ~ spl5_24
    | ~ spl5_25
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f259,f218,f211,f203,f231])).

fof(f203,plain,
    ( spl5_24
  <=> ! [X0] :
        ( r2_hidden(sK4(sK1,X0,sK3),sK1)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f211,plain,
    ( spl5_25
  <=> ! [X0] :
        ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ r2_hidden(k1_funct_1(sK3,sK4(sK1,X0,sK3)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f218,plain,
    ( spl5_26
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f259,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl5_24
    | ~ spl5_25
    | ~ spl5_26 ),
    inference(duplicate_literal_removal,[],[f257])).

fof(f257,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl5_24
    | ~ spl5_25
    | ~ spl5_26 ),
    inference(resolution,[],[f225,f212])).

fof(f212,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_funct_1(sK3,sK4(sK1,X0,sK3)),X0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) )
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f211])).

fof(f225,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,sK4(sK1,X0,sK3)),sK0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) )
    | ~ spl5_24
    | ~ spl5_26 ),
    inference(resolution,[],[f224,f204])).

fof(f204,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK1,X0,sK3),sK1)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) )
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f203])).

fof(f224,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(k1_funct_1(sK3,X0),sK0) )
    | ~ spl5_26 ),
    inference(duplicate_literal_removal,[],[f223])).

fof(f223,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,X0),sK0)
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl5_26 ),
    inference(resolution,[],[f222,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f222,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | r2_hidden(k1_funct_1(sK3,X0),sK0)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl5_26 ),
    inference(superposition,[],[f41,f221])).

fof(f221,plain,
    ( ! [X0] :
        ( k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl5_26 ),
    inference(resolution,[],[f219,f46])).

fof(f219,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0) )
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f218])).

fof(f41,plain,(
    ! [X4] :
      ( r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0)
      | ~ m1_subset_1(X4,sK1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0)
    & ! [X4] :
        ( r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0)
        | ~ m1_subset_1(X4,sK1) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK2)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f31,f30,f29])).

fof(f29,plain,
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
              ( ~ r1_tarski(k2_relset_1(sK1,X2,X3),sK0)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(sK1,X2,X3,X4),sK0)
                  | ~ m1_subset_1(X4,sK1) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
              & v1_funct_2(X3,sK1,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k2_relset_1(sK1,X2,X3),sK0)
            & ! [X4] :
                ( r2_hidden(k3_funct_2(sK1,X2,X3,X4),sK0)
                | ~ m1_subset_1(X4,sK1) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
            & v1_funct_2(X3,sK1,X2)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k2_relset_1(sK1,sK2,X3),sK0)
          & ! [X4] :
              ( r2_hidden(k3_funct_2(sK1,sK2,X3,X4),sK0)
              | ~ m1_subset_1(X4,sK1) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X3,sK1,sK2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k2_relset_1(sK1,sK2,X3),sK0)
        & ! [X4] :
            ( r2_hidden(k3_funct_2(sK1,sK2,X3,X4),sK0)
            | ~ m1_subset_1(X4,sK1) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        & v1_funct_2(X3,sK1,sK2)
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0)
      & ! [X4] :
          ( r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0)
          | ~ m1_subset_1(X4,sK1) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_funct_2)).

fof(f220,plain,
    ( spl5_6
    | spl5_26
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f215,f88,f84,f80,f218,f96])).

fof(f96,plain,
    ( spl5_6
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f80,plain,
    ( spl5_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f84,plain,
    ( spl5_3
  <=> v1_funct_2(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f88,plain,
    ( spl5_4
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f215,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0)
        | v1_xboole_0(sK1) )
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(resolution,[],[f214,f85])).

fof(f85,plain,
    ( v1_funct_2(sK3,sK1,sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f214,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(sK3,X1,X2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ m1_subset_1(X0,X1)
        | k3_funct_2(X1,X2,sK3,X0) = k1_funct_1(sK3,X0)
        | v1_xboole_0(X1) )
    | ~ spl5_4 ),
    inference(resolution,[],[f63,f89])).

fof(f89,plain,
    ( v1_funct_1(sK3)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

% (4520)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f213,plain,
    ( ~ spl5_18
    | spl5_25
    | ~ spl5_4
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f209,f162,f88,f211,f170])).

fof(f170,plain,
    ( spl5_18
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f162,plain,
    ( spl5_17
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f209,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ r2_hidden(k1_funct_1(sK3,sK4(sK1,X0,sK3)),X0)
        | ~ v1_relat_1(sK3) )
    | ~ spl5_4
    | ~ spl5_17 ),
    inference(forward_demodulation,[],[f208,f163])).

fof(f163,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f162])).

fof(f208,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_funct_1(sK3,sK4(sK1,X0,sK3)),X0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))
        | ~ v1_relat_1(sK3) )
    | ~ spl5_4
    | ~ spl5_17 ),
    inference(forward_demodulation,[],[f207,f163])).

fof(f207,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_funct_1(sK3,sK4(k1_relat_1(sK3),X0,sK3)),X0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))
        | ~ v1_relat_1(sK3) )
    | ~ spl5_4 ),
    inference(resolution,[],[f69,f89])).

fof(f69,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(k1_funct_1(X2,sK4(k1_relat_1(X2),X1,X2)),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ( ~ r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1)
        & r2_hidden(sK4(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1)
        & r2_hidden(sK4(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

fof(f206,plain,
    ( k1_xboole_0 != sK2
    | ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f205,plain,
    ( ~ spl5_18
    | ~ spl5_4
    | spl5_24
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f201,f162,f203,f88,f170])).

fof(f201,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK1,X0,sK3),sK1)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3) )
    | ~ spl5_17 ),
    inference(superposition,[],[f70,f163])).

fof(f70,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK4(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK4(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f200,plain,(
    spl5_23 ),
    inference(avatar_contradiction_clause,[],[f198])).

fof(f198,plain,
    ( $false
    | spl5_23 ),
    inference(resolution,[],[f196,f45])).

fof(f45,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f196,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | spl5_23 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl5_23
  <=> v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f197,plain,
    ( ~ spl5_23
    | ~ spl5_2
    | spl5_18 ),
    inference(avatar_split_clause,[],[f192,f170,f80,f195])).

fof(f192,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | ~ spl5_2
    | spl5_18 ),
    inference(resolution,[],[f188,f81])).

fof(f81,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f188,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl5_18 ),
    inference(resolution,[],[f171,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f171,plain,
    ( ~ v1_relat_1(sK3)
    | spl5_18 ),
    inference(avatar_component_clause,[],[f170])).

fof(f165,plain,
    ( ~ spl5_2
    | spl5_17
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f160,f156,f162,f80])).

fof(f156,plain,
    ( spl5_16
  <=> sK1 = k1_relset_1(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f160,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_16 ),
    inference(superposition,[],[f48,f157])).

fof(f157,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f156])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f158,plain,
    ( ~ spl5_2
    | spl5_15
    | spl5_16
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f149,f84,f156,f153,f80])).

fof(f153,plain,
    ( spl5_15
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f149,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_3 ),
    inference(resolution,[],[f51,f85])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f129,plain,
    ( ~ spl5_12
    | spl5_8
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f120,f116,f105,f127])).

fof(f105,plain,
    ( spl5_8
  <=> m1_subset_1(k2_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f116,plain,
    ( spl5_10
  <=> k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f120,plain,
    ( ~ m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK0))
    | spl5_8
    | ~ spl5_10 ),
    inference(superposition,[],[f106,f117])).

fof(f117,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f116])).

fof(f106,plain,
    ( ~ m1_subset_1(k2_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK0))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f105])).

fof(f118,plain,
    ( spl5_10
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f113,f80,f116])).

fof(f113,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)
    | ~ spl5_2 ),
    inference(resolution,[],[f49,f81])).

fof(f107,plain,
    ( ~ spl5_8
    | spl5_1 ),
    inference(avatar_split_clause,[],[f103,f76,f105])).

fof(f76,plain,
    ( spl5_1
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f103,plain,
    ( ~ m1_subset_1(k2_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK0))
    | spl5_1 ),
    inference(resolution,[],[f47,f77])).

fof(f77,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f102,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f43,f100])).

fof(f100,plain,
    ( spl5_7
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f98,plain,(
    ~ spl5_6 ),
    inference(avatar_split_clause,[],[f36,f96])).

fof(f36,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f94,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f37,f92])).

fof(f92,plain,
    ( spl5_5
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f37,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f90,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f38,f88])).

fof(f38,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f86,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f39,f84])).

fof(f39,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f82,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f40,f80])).

fof(f40,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f32])).

fof(f78,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f42,f76])).

fof(f42,plain,(
    ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:10:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (4523)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (4524)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (4521)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (4526)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (4534)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (4523)Refutation not found, incomplete strategy% (4523)------------------------------
% 0.21/0.49  % (4523)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (4523)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.50  % (4523)Memory used [KB]: 10746
% 0.21/0.50  % (4523)Time elapsed: 0.074 s
% 0.21/0.50  % (4523)------------------------------
% 0.21/0.50  % (4523)------------------------------
% 0.21/0.50  % (4530)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.50  % (4525)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (4535)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (4526)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f334,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f78,f82,f86,f90,f94,f98,f102,f107,f118,f129,f158,f165,f197,f200,f205,f206,f213,f220,f260,f327,f333])).
% 0.21/0.50  fof(f333,plain,(
% 0.21/0.50    ~spl5_27 | spl5_12 | ~spl5_41),
% 0.21/0.50    inference(avatar_split_clause,[],[f331,f325,f127,f231])).
% 0.21/0.50  fof(f231,plain,(
% 0.21/0.50    spl5_27 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    spl5_12 <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.50  fof(f325,plain,(
% 0.21/0.50    spl5_41 <=> k2_relat_1(sK3) = k2_relset_1(sK1,sK0,sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 0.21/0.50  fof(f331,plain,(
% 0.21/0.50    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl5_41),
% 0.21/0.50    inference(superposition,[],[f50,f326])).
% 0.21/0.50  fof(f326,plain,(
% 0.21/0.50    k2_relat_1(sK3) = k2_relset_1(sK1,sK0,sK3) | ~spl5_41),
% 0.21/0.50    inference(avatar_component_clause,[],[f325])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.21/0.50  fof(f327,plain,(
% 0.21/0.50    spl5_41 | ~spl5_27),
% 0.21/0.50    inference(avatar_split_clause,[],[f323,f231,f325])).
% 0.21/0.50  fof(f323,plain,(
% 0.21/0.50    k2_relat_1(sK3) = k2_relset_1(sK1,sK0,sK3) | ~spl5_27),
% 0.21/0.50    inference(resolution,[],[f232,f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.50  fof(f232,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl5_27),
% 0.21/0.50    inference(avatar_component_clause,[],[f231])).
% 0.21/0.50  fof(f260,plain,(
% 0.21/0.50    spl5_27 | ~spl5_24 | ~spl5_25 | ~spl5_26),
% 0.21/0.50    inference(avatar_split_clause,[],[f259,f218,f211,f203,f231])).
% 0.21/0.50  fof(f203,plain,(
% 0.21/0.50    spl5_24 <=> ! [X0] : (r2_hidden(sK4(sK1,X0,sK3),sK1) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.21/0.50  fof(f211,plain,(
% 0.21/0.50    spl5_25 <=> ! [X0] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~r2_hidden(k1_funct_1(sK3,sK4(sK1,X0,sK3)),X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.21/0.50  fof(f218,plain,(
% 0.21/0.50    spl5_26 <=> ! [X0] : (~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.21/0.50  fof(f259,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl5_24 | ~spl5_25 | ~spl5_26)),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f257])).
% 0.21/0.50  fof(f257,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl5_24 | ~spl5_25 | ~spl5_26)),
% 0.21/0.50    inference(resolution,[],[f225,f212])).
% 0.21/0.50  fof(f212,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(k1_funct_1(sK3,sK4(sK1,X0,sK3)),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))) ) | ~spl5_25),
% 0.21/0.50    inference(avatar_component_clause,[],[f211])).
% 0.21/0.50  fof(f225,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,sK4(sK1,X0,sK3)),sK0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))) ) | (~spl5_24 | ~spl5_26)),
% 0.21/0.50    inference(resolution,[],[f224,f204])).
% 0.21/0.50  fof(f204,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK4(sK1,X0,sK3),sK1) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))) ) | ~spl5_24),
% 0.21/0.50    inference(avatar_component_clause,[],[f203])).
% 0.21/0.50  fof(f224,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(k1_funct_1(sK3,X0),sK0)) ) | ~spl5_26),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f223])).
% 0.21/0.50  fof(f223,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),sK0) | ~r2_hidden(X0,sK1) | ~r2_hidden(X0,sK1)) ) | ~spl5_26),
% 0.21/0.50    inference(resolution,[],[f222,f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.50  fof(f222,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,sK1) | r2_hidden(k1_funct_1(sK3,X0),sK0) | ~r2_hidden(X0,sK1)) ) | ~spl5_26),
% 0.21/0.50    inference(superposition,[],[f41,f221])).
% 0.21/0.50  fof(f221,plain,(
% 0.21/0.50    ( ! [X0] : (k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0) | ~r2_hidden(X0,sK1)) ) | ~spl5_26),
% 0.21/0.50    inference(resolution,[],[f219,f46])).
% 0.21/0.50  fof(f219,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0)) ) | ~spl5_26),
% 0.21/0.50    inference(avatar_component_clause,[],[f218])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X4] : (r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0) | ~m1_subset_1(X4,sK1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ((~r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) & ! [X4] : (r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0) | ~m1_subset_1(X4,sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f31,f30,f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(sK1,X2,X3),sK0) & ! [X4] : (r2_hidden(k3_funct_2(sK1,X2,X3,X4),sK0) | ~m1_subset_1(X4,sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) & v1_funct_2(X3,sK1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(sK1,X2,X3),sK0) & ! [X4] : (r2_hidden(k3_funct_2(sK1,X2,X3,X4),sK0) | ~m1_subset_1(X4,sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) & v1_funct_2(X3,sK1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (~r1_tarski(k2_relset_1(sK1,sK2,X3),sK0) & ! [X4] : (r2_hidden(k3_funct_2(sK1,sK2,X3,X4),sK0) | ~m1_subset_1(X4,sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & ~v1_xboole_0(sK2))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ? [X3] : (~r1_tarski(k2_relset_1(sK1,sK2,X3),sK0) & ! [X4] : (r2_hidden(k3_funct_2(sK1,sK2,X3,X4),sK0) | ~m1_subset_1(X4,sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) => (~r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) & ! [X4] : (r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0) | ~m1_subset_1(X4,sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 0.21/0.50    inference(flattening,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 0.21/0.50    inference(negated_conjecture,[],[f12])).
% 0.21/0.50  fof(f12,conjecture,(
% 0.21/0.50    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_funct_2)).
% 0.21/0.50  fof(f220,plain,(
% 0.21/0.50    spl5_6 | spl5_26 | ~spl5_2 | ~spl5_3 | ~spl5_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f215,f88,f84,f80,f218,f96])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    spl5_6 <=> v1_xboole_0(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    spl5_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    spl5_3 <=> v1_funct_2(sK3,sK1,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    spl5_4 <=> v1_funct_1(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.50  fof(f215,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0) | v1_xboole_0(sK1)) ) | (~spl5_3 | ~spl5_4)),
% 0.21/0.50    inference(resolution,[],[f214,f85])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    v1_funct_2(sK3,sK1,sK2) | ~spl5_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f84])).
% 0.21/0.50  fof(f214,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_funct_2(sK3,X1,X2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(X0,X1) | k3_funct_2(X1,X2,sK3,X0) = k1_funct_1(sK3,X0) | v1_xboole_0(X1)) ) | ~spl5_4),
% 0.21/0.50    inference(resolution,[],[f63,f89])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    v1_funct_1(sK3) | ~spl5_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f88])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  % (4520)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.21/0.50    inference(flattening,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.21/0.50  fof(f213,plain,(
% 0.21/0.50    ~spl5_18 | spl5_25 | ~spl5_4 | ~spl5_17),
% 0.21/0.50    inference(avatar_split_clause,[],[f209,f162,f88,f211,f170])).
% 0.21/0.50  fof(f170,plain,(
% 0.21/0.50    spl5_18 <=> v1_relat_1(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    spl5_17 <=> sK1 = k1_relat_1(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.50  fof(f209,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~r2_hidden(k1_funct_1(sK3,sK4(sK1,X0,sK3)),X0) | ~v1_relat_1(sK3)) ) | (~spl5_4 | ~spl5_17)),
% 0.21/0.50    inference(forward_demodulation,[],[f208,f163])).
% 0.21/0.50  fof(f163,plain,(
% 0.21/0.50    sK1 = k1_relat_1(sK3) | ~spl5_17),
% 0.21/0.50    inference(avatar_component_clause,[],[f162])).
% 0.21/0.50  fof(f208,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(k1_funct_1(sK3,sK4(sK1,X0,sK3)),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) | ~v1_relat_1(sK3)) ) | (~spl5_4 | ~spl5_17)),
% 0.21/0.50    inference(forward_demodulation,[],[f207,f163])).
% 0.21/0.50  fof(f207,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(k1_funct_1(sK3,sK4(k1_relat_1(sK3),X0,sK3)),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) | ~v1_relat_1(sK3)) ) | ~spl5_4),
% 0.21/0.50    inference(resolution,[],[f69,f89])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ( ! [X2,X1] : (~v1_funct_1(X2) | ~r2_hidden(k1_funct_1(X2,sK4(k1_relat_1(X2),X1,X2)),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | ~v1_relat_1(X2)) )),
% 0.21/0.50    inference(equality_resolution,[],[f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1) & r2_hidden(sK4(X0,X1,X2),X0)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(flattening,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).
% 0.21/0.51  fof(f206,plain,(
% 0.21/0.51    k1_xboole_0 != sK2 | ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(sK2)),
% 0.21/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.51  fof(f205,plain,(
% 0.21/0.51    ~spl5_18 | ~spl5_4 | spl5_24 | ~spl5_17),
% 0.21/0.51    inference(avatar_split_clause,[],[f201,f162,f203,f88,f170])).
% 0.21/0.51  fof(f201,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK4(sK1,X0,sK3),sK1) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) ) | ~spl5_17),
% 0.21/0.51    inference(superposition,[],[f70,f163])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ( ! [X2,X1] : (r2_hidden(sK4(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.51    inference(equality_resolution,[],[f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(sK4(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f35])).
% 0.21/0.51  fof(f200,plain,(
% 0.21/0.51    spl5_23),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f198])).
% 0.21/0.51  fof(f198,plain,(
% 0.21/0.51    $false | spl5_23),
% 0.21/0.51    inference(resolution,[],[f196,f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.51  fof(f196,plain,(
% 0.21/0.51    ~v1_relat_1(k2_zfmisc_1(sK1,sK2)) | spl5_23),
% 0.21/0.51    inference(avatar_component_clause,[],[f195])).
% 0.21/0.51  fof(f195,plain,(
% 0.21/0.51    spl5_23 <=> v1_relat_1(k2_zfmisc_1(sK1,sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.21/0.51  fof(f197,plain,(
% 0.21/0.51    ~spl5_23 | ~spl5_2 | spl5_18),
% 0.21/0.51    inference(avatar_split_clause,[],[f192,f170,f80,f195])).
% 0.21/0.51  fof(f192,plain,(
% 0.21/0.51    ~v1_relat_1(k2_zfmisc_1(sK1,sK2)) | (~spl5_2 | spl5_18)),
% 0.21/0.51    inference(resolution,[],[f188,f81])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f80])).
% 0.21/0.51  fof(f188,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl5_18),
% 0.21/0.51    inference(resolution,[],[f171,f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.51  fof(f171,plain,(
% 0.21/0.51    ~v1_relat_1(sK3) | spl5_18),
% 0.21/0.51    inference(avatar_component_clause,[],[f170])).
% 0.21/0.51  fof(f165,plain,(
% 0.21/0.51    ~spl5_2 | spl5_17 | ~spl5_16),
% 0.21/0.51    inference(avatar_split_clause,[],[f160,f156,f162,f80])).
% 0.21/0.51  fof(f156,plain,(
% 0.21/0.51    spl5_16 <=> sK1 = k1_relset_1(sK1,sK2,sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.51  fof(f160,plain,(
% 0.21/0.51    sK1 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_16),
% 0.21/0.51    inference(superposition,[],[f48,f157])).
% 0.21/0.51  fof(f157,plain,(
% 0.21/0.51    sK1 = k1_relset_1(sK1,sK2,sK3) | ~spl5_16),
% 0.21/0.51    inference(avatar_component_clause,[],[f156])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.51  fof(f158,plain,(
% 0.21/0.51    ~spl5_2 | spl5_15 | spl5_16 | ~spl5_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f149,f84,f156,f153,f80])).
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    spl5_15 <=> k1_xboole_0 = sK2),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.51  fof(f149,plain,(
% 0.21/0.51    sK1 = k1_relset_1(sK1,sK2,sK3) | k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_3),
% 0.21/0.51    inference(resolution,[],[f51,f85])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(nnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(flattening,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.51  fof(f129,plain,(
% 0.21/0.51    ~spl5_12 | spl5_8 | ~spl5_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f120,f116,f105,f127])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    spl5_8 <=> m1_subset_1(k2_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    spl5_10 <=> k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.51  fof(f120,plain,(
% 0.21/0.51    ~m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK0)) | (spl5_8 | ~spl5_10)),
% 0.21/0.51    inference(superposition,[],[f106,f117])).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) | ~spl5_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f116])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    ~m1_subset_1(k2_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK0)) | spl5_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f105])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    spl5_10 | ~spl5_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f113,f80,f116])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) | ~spl5_2),
% 0.21/0.51    inference(resolution,[],[f49,f81])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    ~spl5_8 | spl5_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f103,f76,f105])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    spl5_1 <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    ~m1_subset_1(k2_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK0)) | spl5_1),
% 0.21/0.51    inference(resolution,[],[f47,f77])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    ~r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) | spl5_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f76])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.21/0.51    inference(unused_predicate_definition_removal,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    spl5_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f43,f100])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    spl5_7 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    ~spl5_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f36,f96])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ~v1_xboole_0(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    ~spl5_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f37,f92])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    spl5_5 <=> v1_xboole_0(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ~v1_xboole_0(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    spl5_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f38,f88])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    v1_funct_1(sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    spl5_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f39,f84])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    v1_funct_2(sK3,sK1,sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    spl5_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f40,f80])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ~spl5_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f42,f76])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ~r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (4526)------------------------------
% 0.21/0.51  % (4526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (4526)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (4526)Memory used [KB]: 10874
% 0.21/0.51  % (4526)Time elapsed: 0.040 s
% 0.21/0.51  % (4526)------------------------------
% 0.21/0.51  % (4526)------------------------------
% 0.21/0.51  % (4519)Success in time 0.142 s
%------------------------------------------------------------------------------
