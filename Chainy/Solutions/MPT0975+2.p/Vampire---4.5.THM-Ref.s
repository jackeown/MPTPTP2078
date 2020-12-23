%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0975+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:00 EST 2020

% Result     : Theorem 9.51s
% Output     : Refutation 9.51s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 128 expanded)
%              Number of leaves         :   20 (  55 expanded)
%              Depth                    :    7
%              Number of atoms          :  230 ( 724 expanded)
%              Number of equality atoms :   66 ( 195 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10488,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f4198,f4202,f4206,f4210,f4214,f4218,f4222,f4226,f9998,f10010,f10111,f10460,f10487])).

fof(f10487,plain,
    ( k1_relat_1(sK5) != k1_relset_1(sK2,sK3,sK5)
    | sK2 != k1_relset_1(sK2,sK3,sK5)
    | r2_hidden(sK4,k1_relat_1(sK5))
    | ~ r2_hidden(sK4,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f10460,plain,
    ( ~ spl242_627
    | ~ spl242_8
    | ~ spl242_5
    | ~ spl242_4
    | ~ spl242_1128
    | spl242_1 ),
    inference(avatar_split_clause,[],[f10413,f4196,f10458,f4208,f4212,f4224,f8073])).

fof(f8073,plain,
    ( spl242_627
  <=> v1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl242_627])])).

fof(f4224,plain,
    ( spl242_8
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl242_8])])).

fof(f4212,plain,
    ( spl242_5
  <=> v1_relat_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl242_5])])).

fof(f4208,plain,
    ( spl242_4
  <=> v1_funct_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl242_4])])).

fof(f10458,plain,
    ( spl242_1128
  <=> r2_hidden(sK4,k1_relat_1(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl242_1128])])).

fof(f4196,plain,
    ( spl242_1
  <=> k1_funct_1(k5_relat_1(sK5,sK6),sK4) = k1_funct_1(sK6,k1_funct_1(sK5,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl242_1])])).

fof(f10413,plain,
    ( ~ r2_hidden(sK4,k1_relat_1(sK5))
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | spl242_1 ),
    inference(trivial_inequality_removal,[],[f10404])).

fof(f10404,plain,
    ( k1_funct_1(sK6,k1_funct_1(sK5,sK4)) != k1_funct_1(sK6,k1_funct_1(sK5,sK4))
    | ~ r2_hidden(sK4,k1_relat_1(sK5))
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | spl242_1 ),
    inference(superposition,[],[f4197,f2770])).

fof(f2770,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1532])).

fof(f1532,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1531])).

fof(f1531,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1006])).

fof(f1006,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

fof(f4197,plain,
    ( k1_funct_1(k5_relat_1(sK5,sK6),sK4) != k1_funct_1(sK6,k1_funct_1(sK5,sK4))
    | spl242_1 ),
    inference(avatar_component_clause,[],[f4196])).

fof(f10111,plain,
    ( spl242_1049
    | ~ spl242_6 ),
    inference(avatar_split_clause,[],[f9926,f4216,f10109])).

fof(f10109,plain,
    ( spl242_1049
  <=> k1_relat_1(sK5) = k1_relset_1(sK2,sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl242_1049])])).

fof(f4216,plain,
    ( spl242_6
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl242_6])])).

fof(f9926,plain,
    ( k1_relat_1(sK5) = k1_relset_1(sK2,sK3,sK5)
    | ~ spl242_6 ),
    inference(resolution,[],[f4217,f3716])).

fof(f3716,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2125])).

fof(f2125,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1227])).

fof(f1227,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f4217,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ spl242_6 ),
    inference(avatar_component_clause,[],[f4216])).

fof(f10010,plain,
    ( spl242_2
    | ~ spl242_7
    | spl242_1023
    | ~ spl242_6 ),
    inference(avatar_split_clause,[],[f9901,f4216,f9886,f4220,f4200])).

fof(f4200,plain,
    ( spl242_2
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl242_2])])).

fof(f4220,plain,
    ( spl242_7
  <=> v1_funct_2(sK5,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl242_7])])).

fof(f9886,plain,
    ( spl242_1023
  <=> sK2 = k1_relset_1(sK2,sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl242_1023])])).

fof(f9901,plain,
    ( sK2 = k1_relset_1(sK2,sK3,sK5)
    | ~ v1_funct_2(sK5,sK2,sK3)
    | k1_xboole_0 = sK3
    | ~ spl242_6 ),
    inference(resolution,[],[f4217,f3089])).

fof(f3089,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2432])).

fof(f2432,plain,(
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
    inference(nnf_transformation,[],[f1716])).

fof(f1716,plain,(
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
    inference(flattening,[],[f1715])).

fof(f1715,plain,(
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
    inference(ennf_transformation,[],[f1471])).

fof(f1471,axiom,(
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

fof(f9998,plain,
    ( spl242_627
    | ~ spl242_6 ),
    inference(avatar_split_clause,[],[f9890,f4216,f8073])).

fof(f9890,plain,
    ( v1_relat_1(sK5)
    | ~ spl242_6 ),
    inference(resolution,[],[f4217,f3031])).

fof(f3031,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1680])).

fof(f1680,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1210])).

fof(f1210,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f4226,plain,(
    spl242_8 ),
    inference(avatar_split_clause,[],[f2741,f4224])).

fof(f2741,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f2287])).

fof(f2287,plain,
    ( k1_funct_1(k5_relat_1(sK5,sK6),sK4) != k1_funct_1(sK6,k1_funct_1(sK5,sK4))
    & k1_xboole_0 != sK3
    & r2_hidden(sK4,sK2)
    & v1_funct_1(sK6)
    & v1_relat_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK5,sK2,sK3)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f1509,f2286,f2285])).

fof(f2285,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( k1_funct_1(k5_relat_1(X3,X4),X2) != k1_funct_1(X4,k1_funct_1(X3,X2))
            & k1_xboole_0 != X1
            & r2_hidden(X2,X0)
            & v1_funct_1(X4)
            & v1_relat_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( k1_funct_1(k5_relat_1(sK5,X4),sK4) != k1_funct_1(X4,k1_funct_1(sK5,sK4))
          & k1_xboole_0 != sK3
          & r2_hidden(sK4,sK2)
          & v1_funct_1(X4)
          & v1_relat_1(X4) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK5,sK2,sK3)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f2286,plain,
    ( ? [X4] :
        ( k1_funct_1(k5_relat_1(sK5,X4),sK4) != k1_funct_1(X4,k1_funct_1(sK5,sK4))
        & k1_xboole_0 != sK3
        & r2_hidden(sK4,sK2)
        & v1_funct_1(X4)
        & v1_relat_1(X4) )
   => ( k1_funct_1(k5_relat_1(sK5,sK6),sK4) != k1_funct_1(sK6,k1_funct_1(sK5,sK4))
      & k1_xboole_0 != sK3
      & r2_hidden(sK4,sK2)
      & v1_funct_1(sK6)
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f1509,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k1_funct_1(k5_relat_1(X3,X4),X2) != k1_funct_1(X4,k1_funct_1(X3,X2))
          & k1_xboole_0 != X1
          & r2_hidden(X2,X0)
          & v1_funct_1(X4)
          & v1_relat_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f1508])).

fof(f1508,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k1_funct_1(k5_relat_1(X3,X4),X2) != k1_funct_1(X4,k1_funct_1(X3,X2))
          & k1_xboole_0 != X1
          & r2_hidden(X2,X0)
          & v1_funct_1(X4)
          & v1_relat_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f1489])).

fof(f1489,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_relat_1(X4) )
           => ( r2_hidden(X2,X0)
             => ( k1_funct_1(k5_relat_1(X3,X4),X2) = k1_funct_1(X4,k1_funct_1(X3,X2))
                | k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f1488])).

fof(f1488,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_relat_1(X4) )
         => ( r2_hidden(X2,X0)
           => ( k1_funct_1(k5_relat_1(X3,X4),X2) = k1_funct_1(X4,k1_funct_1(X3,X2))
              | k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_2)).

fof(f4222,plain,(
    spl242_7 ),
    inference(avatar_split_clause,[],[f2742,f4220])).

fof(f2742,plain,(
    v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f2287])).

fof(f4218,plain,(
    spl242_6 ),
    inference(avatar_split_clause,[],[f2743,f4216])).

fof(f2743,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f2287])).

fof(f4214,plain,(
    spl242_5 ),
    inference(avatar_split_clause,[],[f2744,f4212])).

fof(f2744,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f2287])).

fof(f4210,plain,(
    spl242_4 ),
    inference(avatar_split_clause,[],[f2745,f4208])).

fof(f2745,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f2287])).

fof(f4206,plain,(
    spl242_3 ),
    inference(avatar_split_clause,[],[f2746,f4204])).

fof(f4204,plain,
    ( spl242_3
  <=> r2_hidden(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl242_3])])).

fof(f2746,plain,(
    r2_hidden(sK4,sK2) ),
    inference(cnf_transformation,[],[f2287])).

fof(f4202,plain,(
    ~ spl242_2 ),
    inference(avatar_split_clause,[],[f2747,f4200])).

fof(f2747,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f2287])).

fof(f4198,plain,(
    ~ spl242_1 ),
    inference(avatar_split_clause,[],[f2748,f4196])).

fof(f2748,plain,(
    k1_funct_1(k5_relat_1(sK5,sK6),sK4) != k1_funct_1(sK6,k1_funct_1(sK5,sK4)) ),
    inference(cnf_transformation,[],[f2287])).
%------------------------------------------------------------------------------
