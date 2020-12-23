%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1025+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:06 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 125 expanded)
%              Number of leaves         :   15 (  55 expanded)
%              Depth                    :    9
%              Number of atoms          :  282 ( 666 expanded)
%              Number of equality atoms :   37 (  95 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f75,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f27,f31,f35,f39,f46,f53,f59,f65,f71,f74])).

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
        ( ~ r2_hidden(X0,k7_relset_1(sK0,sK1,sK3,sK2))
        | sK4 != X0 ) ),
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
    ( spl6_9
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f67,f63,f33,f29,f69])).

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
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_funct_2(sK3,sK0,X0)
        | ~ r2_hidden(X1,k7_relset_1(sK0,sK1,sK3,sK2))
        | ~ r2_hidden(X1,k7_relset_1(sK0,X0,sK3,sK2))
        | sK4 != X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f67,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ r2_hidden(X0,k7_relset_1(sK0,sK1,sK3,sK2))
        | sK4 != X0 )
    | ~ spl6_3
    | ~ spl6_8 ),
    inference(duplicate_literal_removal,[],[f66])).

fof(f66,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ r2_hidden(X0,k7_relset_1(sK0,sK1,sK3,sK2))
        | ~ r2_hidden(X0,k7_relset_1(sK0,sK1,sK3,sK2))
        | sK4 != X0 )
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
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ r2_hidden(X1,k7_relset_1(sK0,sK1,sK3,sK2))
        | ~ r2_hidden(X1,k7_relset_1(sK0,X0,sK3,sK2))
        | sK4 != X1 )
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
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_funct_2(sK3,sK0,X2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
        | ~ r2_hidden(X1,k7_relset_1(sK0,X2,sK3,sK2))
        | ~ v1_funct_2(sK3,sK0,X0)
        | sK4 != X1
        | ~ r2_hidden(X1,k7_relset_1(sK0,sK1,sK3,sK2))
        | ~ r2_hidden(X1,k7_relset_1(sK0,X0,sK3,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f61,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ r2_hidden(X1,k7_relset_1(sK0,sK1,sK3,sK2))
        | ~ v1_funct_2(sK3,sK0,X0)
        | sK4 != X1
        | ~ r2_hidden(X1,k7_relset_1(sK0,X0,sK3,sK2)) )
    | ~ spl6_3
    | ~ spl6_7 ),
    inference(duplicate_literal_removal,[],[f60])).

fof(f60,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ r2_hidden(X1,k7_relset_1(sK0,sK1,sK3,sK2))
        | ~ v1_funct_2(sK3,sK0,X0)
        | sK4 != X1
        | ~ r2_hidden(X1,k7_relset_1(sK0,sK1,sK3,sK2))
        | ~ r2_hidden(X1,k7_relset_1(sK0,X0,sK3,sK2)) )
    | ~ spl6_3
    | ~ spl6_7 ),
    inference(resolution,[],[f58,f34])).

fof(f58,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(sK3,sK0,X2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
        | ~ r2_hidden(X1,k7_relset_1(sK0,X2,sK3,sK2))
        | ~ v1_funct_2(sK3,sK0,X0)
        | sK4 != X1
        | ~ r2_hidden(X1,k7_relset_1(sK0,sK1,sK3,sK2))
        | ~ r2_hidden(X1,k7_relset_1(sK0,X0,sK3,sK2)) )
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f57])).

fof(f59,plain,
    ( ~ spl6_4
    | spl6_7
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f55,f51,f57,f37])).

fof(f37,plain,
    ( spl6_4
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f51,plain,
    ( spl6_6
  <=> ! [X1,X0] :
        ( sK4 != X0
        | ~ v1_funct_2(sK3,sK0,X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ r2_hidden(X0,k7_relset_1(sK0,X1,sK3,sK2))
        | ~ r2_hidden(X0,k7_relset_1(sK0,sK1,sK3,sK2))
        | ~ m1_subset_1(sK5(sK0,sK2,sK3,X0),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f55,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ r2_hidden(X1,k7_relset_1(sK0,X0,sK3,sK2))
        | ~ r2_hidden(X1,k7_relset_1(sK0,sK1,sK3,sK2))
        | sK4 != X1
        | ~ v1_funct_2(sK3,sK0,X0)
        | ~ r2_hidden(X1,k7_relset_1(sK0,X2,sK3,sK2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
        | ~ v1_funct_2(sK3,sK0,X2)
        | ~ v1_funct_1(sK3) )
    | ~ spl6_6 ),
    inference(resolution,[],[f54,f21])).

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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f54,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK5(sK0,sK2,sK3,X1),sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ r2_hidden(X1,k7_relset_1(sK0,X0,sK3,sK2))
        | ~ r2_hidden(X1,k7_relset_1(sK0,sK1,sK3,sK2))
        | sK4 != X1
        | ~ v1_funct_2(sK3,sK0,X0) )
    | ~ spl6_6 ),
    inference(resolution,[],[f52,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f52,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK5(sK0,sK2,sK3,X0),sK0)
        | ~ v1_funct_2(sK3,sK0,X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ r2_hidden(X0,k7_relset_1(sK0,X1,sK3,sK2))
        | ~ r2_hidden(X0,k7_relset_1(sK0,sK1,sK3,sK2))
        | sK4 != X0 )
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f51])).

fof(f53,plain,
    ( ~ spl6_4
    | spl6_6
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f48,f43,f51,f37])).

fof(f43,plain,
    ( spl6_5
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k7_relset_1(sK0,sK1,sK3,X1))
        | k1_funct_1(sK3,sK5(sK0,X1,sK3,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f48,plain,
    ( ! [X0,X1] :
        ( sK4 != X0
        | ~ m1_subset_1(sK5(sK0,sK2,sK3,X0),sK0)
        | ~ r2_hidden(X0,k7_relset_1(sK0,sK1,sK3,sK2))
        | ~ r2_hidden(X0,k7_relset_1(sK0,X1,sK3,sK2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ v1_funct_2(sK3,sK0,X1)
        | ~ v1_funct_1(sK3) )
    | ~ spl6_5 ),
    inference(resolution,[],[f47,f22])).

fof(f22,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(sK5(X0,X2,X3,X4),X2)
      | ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f47,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK5(sK0,X0,sK3,X1),sK2)
        | sK4 != X1
        | ~ m1_subset_1(sK5(sK0,X0,sK3,X1),sK0)
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
