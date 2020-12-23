%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 125 expanded)
%              Number of leaves         :   15 (  55 expanded)
%              Depth                    :   10
%              Number of atoms          :  280 ( 664 expanded)
%              Number of equality atoms :   37 (  95 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f75,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f27,f31,f35,f39,f46,f54,f59,f65,f71,f74])).

fof(f74,plain,
    ( ~ spl6_1
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f72,f69,f25])).

fof(f25,plain,
    ( spl6_1
  <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f69,plain,
    ( spl6_9
  <=> ! [X0] :
        ( sK4 != X0
        | ~ r2_hidden(X0,k7_relset_1(sK0,sK1,sK3,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f72,plain,
    ( ~ r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    | ~ spl6_9 ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,
    ( ! [X0] :
        ( sK4 != X0
        | ~ r2_hidden(X0,k7_relset_1(sK0,sK1,sK3,sK2)) )
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f69])).

fof(f71,plain,
    ( ~ spl6_2
    | spl6_9
    | ~ spl6_3
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f67,f63,f33,f69,f29])).

fof(f29,plain,
    ( spl6_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f33,plain,
    ( spl6_3
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f63,plain,
    ( spl6_8
  <=> ! [X1,X0] :
        ( ~ v1_funct_2(sK3,sK0,X0)
        | sK4 != X1
        | ~ r2_hidden(X1,k7_relset_1(sK0,sK1,sK3,sK2))
        | ~ r2_hidden(X1,k7_relset_1(sK0,X0,sK3,sK2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f67,plain,
    ( ! [X0] :
        ( sK4 != X0
        | ~ r2_hidden(X0,k7_relset_1(sK0,sK1,sK3,sK2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
    | ~ spl6_3
    | ~ spl6_8 ),
    inference(duplicate_literal_removal,[],[f66])).

fof(f66,plain,
    ( ! [X0] :
        ( sK4 != X0
        | ~ r2_hidden(X0,k7_relset_1(sK0,sK1,sK3,sK2))
        | ~ r2_hidden(X0,k7_relset_1(sK0,sK1,sK3,sK2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
    | ~ spl6_3
    | ~ spl6_8 ),
    inference(resolution,[],[f64,f34])).

fof(f34,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f33])).

fof(f64,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK3,sK0,X0)
        | sK4 != X1
        | ~ r2_hidden(X1,k7_relset_1(sK0,sK1,sK3,sK2))
        | ~ r2_hidden(X1,k7_relset_1(sK0,X0,sK3,sK2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) )
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f63])).

fof(f65,plain,
    ( ~ spl6_2
    | spl6_8
    | ~ spl6_3
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f61,f57,f33,f63,f29])).

fof(f57,plain,
    ( spl6_7
  <=> ! [X1,X0,X2] :
        ( ~ v1_funct_2(sK3,sK0,X0)
        | ~ v1_funct_2(sK3,sK0,X2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
        | ~ r2_hidden(X1,k7_relset_1(sK0,X2,sK3,sK2))
        | ~ r2_hidden(X1,k7_relset_1(sK0,sK1,sK3,sK2))
        | sK4 != X1
        | ~ r2_hidden(X1,k7_relset_1(sK0,X0,sK3,sK2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f61,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK3,sK0,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ r2_hidden(X1,k7_relset_1(sK0,X0,sK3,sK2))
        | ~ r2_hidden(X1,k7_relset_1(sK0,sK1,sK3,sK2))
        | sK4 != X1
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
    | ~ spl6_3
    | ~ spl6_7 ),
    inference(duplicate_literal_removal,[],[f60])).

fof(f60,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK3,sK0,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ r2_hidden(X1,k7_relset_1(sK0,X0,sK3,sK2))
        | ~ r2_hidden(X1,k7_relset_1(sK0,sK1,sK3,sK2))
        | sK4 != X1
        | ~ r2_hidden(X1,k7_relset_1(sK0,sK1,sK3,sK2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
    | ~ spl6_3
    | ~ spl6_7 ),
    inference(resolution,[],[f58,f34])).

fof(f58,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(sK3,sK0,X0)
        | ~ v1_funct_2(sK3,sK0,X2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
        | ~ r2_hidden(X1,k7_relset_1(sK0,X2,sK3,sK2))
        | ~ r2_hidden(X1,k7_relset_1(sK0,sK1,sK3,sK2))
        | sK4 != X1
        | ~ r2_hidden(X1,k7_relset_1(sK0,X0,sK3,sK2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) )
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f57])).

fof(f59,plain,
    ( ~ spl6_4
    | spl6_7
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f55,f52,f57,f37])).

fof(f37,plain,
    ( spl6_4
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f52,plain,
    ( spl6_6
  <=> ! [X1,X0] :
        ( sK4 != X0
        | ~ v1_funct_2(sK3,sK0,X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ r2_hidden(X0,k7_relset_1(sK0,X1,sK3,sK2))
        | ~ r2_hidden(sK5(sK0,sK2,sK3,X0),sK0)
        | ~ r2_hidden(X0,k7_relset_1(sK0,sK1,sK3,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f55,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(sK3,sK0,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ r2_hidden(X1,k7_relset_1(sK0,X0,sK3,sK2))
        | sK4 != X1
        | ~ r2_hidden(X1,k7_relset_1(sK0,sK1,sK3,sK2))
        | ~ r2_hidden(X1,k7_relset_1(sK0,X2,sK3,sK2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
        | ~ v1_funct_2(sK3,sK0,X2)
        | ~ v1_funct_1(sK3) )
    | ~ spl6_6 ),
    inference(resolution,[],[f53,f21])).

fof(f21,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(sK5(X0,X2,X3,X4),X0)
      | ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( k1_funct_1(X3,sK5(X0,X2,X3,X4)) = X4
            & r2_hidden(sK5(X0,X2,X3,X4),X2)
            & r2_hidden(sK5(X0,X2,X3,X4),X0) )
          | ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f9,f13])).

fof(f13,plain,(
    ! [X4,X3,X2,X0] :
      ( ? [X5] :
          ( k1_funct_1(X3,X5) = X4
          & r2_hidden(X5,X2)
          & r2_hidden(X5,X0) )
     => ( k1_funct_1(X3,sK5(X0,X2,X3,X4)) = X4
        & r2_hidden(sK5(X0,X2,X3,X4),X2)
        & r2_hidden(sK5(X0,X2,X3,X4),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ? [X5] :
              ( k1_funct_1(X3,X5) = X4
              & r2_hidden(X5,X2)
              & r2_hidden(X5,X0) )
          | ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ? [X5] :
              ( k1_funct_1(X3,X5) = X4
              & r2_hidden(X5,X2)
              & r2_hidden(X5,X0) )
          | ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ~ ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).

fof(f53,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK5(sK0,sK2,sK3,X0),sK0)
        | ~ v1_funct_2(sK3,sK0,X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ r2_hidden(X0,k7_relset_1(sK0,X1,sK3,sK2))
        | sK4 != X0
        | ~ r2_hidden(X0,k7_relset_1(sK0,sK1,sK3,sK2)) )
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f52])).

fof(f54,plain,
    ( ~ spl6_4
    | spl6_6
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f49,f43,f52,f37])).

fof(f43,plain,
    ( spl6_5
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k7_relset_1(sK0,sK1,sK3,X1))
        | k1_funct_1(sK3,sK5(sK0,X1,sK3,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f49,plain,
    ( ! [X0,X1] :
        ( sK4 != X0
        | ~ r2_hidden(X0,k7_relset_1(sK0,sK1,sK3,sK2))
        | ~ r2_hidden(sK5(sK0,sK2,sK3,X0),sK0)
        | ~ r2_hidden(X0,k7_relset_1(sK0,X1,sK3,sK2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ v1_funct_2(sK3,sK0,X1)
        | ~ v1_funct_1(sK3) )
    | ~ spl6_5 ),
    inference(resolution,[],[f48,f22])).

fof(f22,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(sK5(X0,X2,X3,X4),X2)
      | ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f48,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK5(sK0,X0,sK3,X1),sK2)
        | sK4 != X1
        | ~ r2_hidden(X1,k7_relset_1(sK0,sK1,sK3,X0))
        | ~ r2_hidden(sK5(sK0,X0,sK3,X1),sK0) )
    | ~ spl6_5 ),
    inference(resolution,[],[f47,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f47,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK5(sK0,X0,sK3,X1),sK0)
        | ~ r2_hidden(sK5(sK0,X0,sK3,X1),sK2)
        | sK4 != X1
        | ~ r2_hidden(X1,k7_relset_1(sK0,sK1,sK3,X0)) )
    | ~ spl6_5 ),
    inference(superposition,[],[f19,f44])).

fof(f44,plain,
    ( ! [X0,X1] :
        ( k1_funct_1(sK3,sK5(sK0,X1,sK3,X0)) = X0
        | ~ r2_hidden(X0,k7_relset_1(sK0,sK1,sK3,X1)) )
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f43])).

fof(f19,plain,(
    ! [X5] :
      ( k1_funct_1(sK3,X5) != sK4
      | ~ r2_hidden(X5,sK2)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ! [X5] :
        ( k1_funct_1(sK3,X5) != sK4
        | ~ r2_hidden(X5,sK2)
        | ~ m1_subset_1(X5,sK0) )
    & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f6,f11,f10])).

fof(f10,plain,
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

fof(f11,plain,
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

fof(f6,plain,(
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
    inference(flattening,[],[f5])).

fof(f5,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
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
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
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

fof(f46,plain,
    ( spl6_5
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f41,f37,f33,f29,f43])).

fof(f41,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ r2_hidden(X0,k7_relset_1(sK0,sK1,sK3,X1))
        | k1_funct_1(sK3,sK5(sK0,X1,sK3,X0)) = X0 )
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(resolution,[],[f40,f34])).

fof(f40,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_funct_2(sK3,X1,X2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ r2_hidden(X0,k7_relset_1(X1,X2,sK3,X3))
        | k1_funct_1(sK3,sK5(X1,X3,sK3,X0)) = X0 )
    | ~ spl6_4 ),
    inference(resolution,[],[f23,f38])).

fof(f38,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f37])).

fof(f23,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | k1_funct_1(X3,sK5(X0,X2,X3,X4)) = X4 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f39,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f15,f37])).

fof(f15,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f35,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f16,f33])).

fof(f16,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f31,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f17,f29])).

fof(f17,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f12])).

fof(f27,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f18,f25])).

fof(f18,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:40:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (30173)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (30187)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.48  % (30174)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (30172)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (30179)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.48  % (30174)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f27,f31,f35,f39,f46,f54,f59,f65,f71,f74])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    ~spl6_1 | ~spl6_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f72,f69,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    spl6_1 <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    spl6_9 <=> ! [X0] : (sK4 != X0 | ~r2_hidden(X0,k7_relset_1(sK0,sK1,sK3,sK2)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    ~r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) | ~spl6_9),
% 0.21/0.48    inference(equality_resolution,[],[f70])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ( ! [X0] : (sK4 != X0 | ~r2_hidden(X0,k7_relset_1(sK0,sK1,sK3,sK2))) ) | ~spl6_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f69])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    ~spl6_2 | spl6_9 | ~spl6_3 | ~spl6_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f67,f63,f33,f69,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    spl6_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    spl6_3 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    spl6_8 <=> ! [X1,X0] : (~v1_funct_2(sK3,sK0,X0) | sK4 != X1 | ~r2_hidden(X1,k7_relset_1(sK0,sK1,sK3,sK2)) | ~r2_hidden(X1,k7_relset_1(sK0,X0,sK3,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ( ! [X0] : (sK4 != X0 | ~r2_hidden(X0,k7_relset_1(sK0,sK1,sK3,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ) | (~spl6_3 | ~spl6_8)),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f66])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ( ! [X0] : (sK4 != X0 | ~r2_hidden(X0,k7_relset_1(sK0,sK1,sK3,sK2)) | ~r2_hidden(X0,k7_relset_1(sK0,sK1,sK3,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ) | (~spl6_3 | ~spl6_8)),
% 0.21/0.48    inference(resolution,[],[f64,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    v1_funct_2(sK3,sK0,sK1) | ~spl6_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f33])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_funct_2(sK3,sK0,X0) | sK4 != X1 | ~r2_hidden(X1,k7_relset_1(sK0,sK1,sK3,sK2)) | ~r2_hidden(X1,k7_relset_1(sK0,X0,sK3,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))) ) | ~spl6_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f63])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ~spl6_2 | spl6_8 | ~spl6_3 | ~spl6_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f61,f57,f33,f63,f29])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    spl6_7 <=> ! [X1,X0,X2] : (~v1_funct_2(sK3,sK0,X0) | ~v1_funct_2(sK3,sK0,X2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) | ~r2_hidden(X1,k7_relset_1(sK0,X2,sK3,sK2)) | ~r2_hidden(X1,k7_relset_1(sK0,sK1,sK3,sK2)) | sK4 != X1 | ~r2_hidden(X1,k7_relset_1(sK0,X0,sK3,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_funct_2(sK3,sK0,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~r2_hidden(X1,k7_relset_1(sK0,X0,sK3,sK2)) | ~r2_hidden(X1,k7_relset_1(sK0,sK1,sK3,sK2)) | sK4 != X1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ) | (~spl6_3 | ~spl6_7)),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_funct_2(sK3,sK0,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~r2_hidden(X1,k7_relset_1(sK0,X0,sK3,sK2)) | ~r2_hidden(X1,k7_relset_1(sK0,sK1,sK3,sK2)) | sK4 != X1 | ~r2_hidden(X1,k7_relset_1(sK0,sK1,sK3,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ) | (~spl6_3 | ~spl6_7)),
% 0.21/0.48    inference(resolution,[],[f58,f34])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_funct_2(sK3,sK0,X0) | ~v1_funct_2(sK3,sK0,X2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) | ~r2_hidden(X1,k7_relset_1(sK0,X2,sK3,sK2)) | ~r2_hidden(X1,k7_relset_1(sK0,sK1,sK3,sK2)) | sK4 != X1 | ~r2_hidden(X1,k7_relset_1(sK0,X0,sK3,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))) ) | ~spl6_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f57])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ~spl6_4 | spl6_7 | ~spl6_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f55,f52,f57,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    spl6_4 <=> v1_funct_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    spl6_6 <=> ! [X1,X0] : (sK4 != X0 | ~v1_funct_2(sK3,sK0,X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~r2_hidden(X0,k7_relset_1(sK0,X1,sK3,sK2)) | ~r2_hidden(sK5(sK0,sK2,sK3,X0),sK0) | ~r2_hidden(X0,k7_relset_1(sK0,sK1,sK3,sK2)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_funct_2(sK3,sK0,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~r2_hidden(X1,k7_relset_1(sK0,X0,sK3,sK2)) | sK4 != X1 | ~r2_hidden(X1,k7_relset_1(sK0,sK1,sK3,sK2)) | ~r2_hidden(X1,k7_relset_1(sK0,X2,sK3,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) | ~v1_funct_2(sK3,sK0,X2) | ~v1_funct_1(sK3)) ) | ~spl6_6),
% 0.21/0.48    inference(resolution,[],[f53,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(sK5(X0,X2,X3,X4),X0) | ~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (! [X4] : ((k1_funct_1(X3,sK5(X0,X2,X3,X4)) = X4 & r2_hidden(sK5(X0,X2,X3,X4),X2) & r2_hidden(sK5(X0,X2,X3,X4),X0)) | ~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f9,f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X4,X3,X2,X0] : (? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) => (k1_funct_1(X3,sK5(X0,X2,X3,X4)) = X4 & r2_hidden(sK5(X0,X2,X3,X4),X2) & r2_hidden(sK5(X0,X2,X3,X4),X0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (! [X4] : (? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) | ~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.48    inference(flattening,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (! [X4] : (? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) | ~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(sK5(sK0,sK2,sK3,X0),sK0) | ~v1_funct_2(sK3,sK0,X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~r2_hidden(X0,k7_relset_1(sK0,X1,sK3,sK2)) | sK4 != X0 | ~r2_hidden(X0,k7_relset_1(sK0,sK1,sK3,sK2))) ) | ~spl6_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f52])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ~spl6_4 | spl6_6 | ~spl6_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f49,f43,f52,f37])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    spl6_5 <=> ! [X1,X0] : (~r2_hidden(X0,k7_relset_1(sK0,sK1,sK3,X1)) | k1_funct_1(sK3,sK5(sK0,X1,sK3,X0)) = X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X0,X1] : (sK4 != X0 | ~r2_hidden(X0,k7_relset_1(sK0,sK1,sK3,sK2)) | ~r2_hidden(sK5(sK0,sK2,sK3,X0),sK0) | ~r2_hidden(X0,k7_relset_1(sK0,X1,sK3,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~v1_funct_2(sK3,sK0,X1) | ~v1_funct_1(sK3)) ) | ~spl6_5),
% 0.21/0.48    inference(resolution,[],[f48,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(sK5(X0,X2,X3,X4),X2) | ~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(sK5(sK0,X0,sK3,X1),sK2) | sK4 != X1 | ~r2_hidden(X1,k7_relset_1(sK0,sK1,sK3,X0)) | ~r2_hidden(sK5(sK0,X0,sK3,X1),sK0)) ) | ~spl6_5),
% 0.21/0.48    inference(resolution,[],[f47,f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(sK5(sK0,X0,sK3,X1),sK0) | ~r2_hidden(sK5(sK0,X0,sK3,X1),sK2) | sK4 != X1 | ~r2_hidden(X1,k7_relset_1(sK0,sK1,sK3,X0))) ) | ~spl6_5),
% 0.21/0.48    inference(superposition,[],[f19,f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_funct_1(sK3,sK5(sK0,X1,sK3,X0)) = X0 | ~r2_hidden(X0,k7_relset_1(sK0,sK1,sK3,X1))) ) | ~spl6_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f43])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ( ! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    (! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f6,f11,f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ? [X4] : (! [X5] : (k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2))) => (! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f6,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.48    inference(flattening,[],[f5])).
% 0.21/0.48  fof(f5,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.48    inference(negated_conjecture,[],[f3])).
% 0.21/0.48  fof(f3,conjecture,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    spl6_5 | ~spl6_2 | ~spl6_3 | ~spl6_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f41,f37,f33,f29,f43])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_hidden(X0,k7_relset_1(sK0,sK1,sK3,X1)) | k1_funct_1(sK3,sK5(sK0,X1,sK3,X0)) = X0) ) | (~spl6_3 | ~spl6_4)),
% 0.21/0.48    inference(resolution,[],[f40,f34])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~v1_funct_2(sK3,X1,X2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r2_hidden(X0,k7_relset_1(X1,X2,sK3,X3)) | k1_funct_1(sK3,sK5(X1,X3,sK3,X0)) = X0) ) | ~spl6_4),
% 0.21/0.48    inference(resolution,[],[f23,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    v1_funct_1(sK3) | ~spl6_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f37])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X3) | ~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | k1_funct_1(X3,sK5(X0,X2,X3,X4)) = X4) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    spl6_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f15,f37])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    v1_funct_1(sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    spl6_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f16,f33])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    spl6_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f17,f29])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    spl6_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f18,f25])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (30174)------------------------------
% 0.21/0.48  % (30174)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (30174)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (30174)Memory used [KB]: 10618
% 0.21/0.48  % (30174)Time elapsed: 0.073 s
% 0.21/0.48  % (30174)------------------------------
% 0.21/0.48  % (30174)------------------------------
% 0.21/0.49  % (30188)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (30181)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (30167)Success in time 0.131 s
%------------------------------------------------------------------------------
