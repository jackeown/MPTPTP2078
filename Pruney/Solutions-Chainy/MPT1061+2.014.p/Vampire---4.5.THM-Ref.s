%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:34 EST 2020

% Result     : Theorem 1.78s
% Output     : Refutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 714 expanded)
%              Number of leaves         :   30 ( 214 expanded)
%              Depth                    :   20
%              Number of atoms          :  553 (4147 expanded)
%              Number of equality atoms :  119 ( 465 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f571,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f105,f132,f139,f181,f197,f289,f330,f332,f350,f547,f568])).

fof(f568,plain,
    ( spl5_3
    | ~ spl5_12 ),
    inference(avatar_contradiction_clause,[],[f567])).

fof(f567,plain,
    ( $false
    | spl5_3
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f206,f562])).

fof(f562,plain,
    ( ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl5_3 ),
    inference(forward_demodulation,[],[f104,f154])).

fof(f154,plain,(
    ! [X2] : k7_relat_1(sK4,X2) = k2_partfun1(sK0,sK3,sK4,X2) ),
    inference(subsumption_resolution,[],[f145,f50])).

fof(f50,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) )
    & r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)
    & r1_tarski(sK1,sK0)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    & v1_funct_2(sK4,sK0,sK3)
    & v1_funct_1(sK4)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f23,f41,f40])).

fof(f40,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
              | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
            & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
            & r1_tarski(X1,X0)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
            & v1_funct_2(X4,X0,X3)
            & v1_funct_1(X4) )
        & ~ v1_xboole_0(X3) )
   => ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(sK0,sK3,X4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
            | ~ v1_funct_2(k2_partfun1(sK0,sK3,X4,sK1),sK1,sK2)
            | ~ v1_funct_1(k2_partfun1(sK0,sK3,X4,sK1)) )
          & r1_tarski(k7_relset_1(sK0,sK3,X4,sK1),sK2)
          & r1_tarski(sK1,sK0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
          & v1_funct_2(X4,sK0,sK3)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X4] :
        ( ( ~ m1_subset_1(k2_partfun1(sK0,sK3,X4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          | ~ v1_funct_2(k2_partfun1(sK0,sK3,X4,sK1),sK1,sK2)
          | ~ v1_funct_1(k2_partfun1(sK0,sK3,X4,sK1)) )
        & r1_tarski(k7_relset_1(sK0,sK3,X4,sK1),sK2)
        & r1_tarski(sK1,sK0)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
        & v1_funct_2(X4,sK0,sK3)
        & v1_funct_1(X4) )
   => ( ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
        | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) )
      & r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)
      & r1_tarski(sK1,sK0)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
      & v1_funct_2(sK4,sK0,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
            | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
          & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
          & r1_tarski(X1,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
          & v1_funct_2(X4,X0,X3)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(X3) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
            | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
          & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
          & r1_tarski(X1,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
          & v1_funct_2(X4,X0,X3)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(X3) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ~ v1_xboole_0(X3)
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
              & v1_funct_2(X4,X0,X3)
              & v1_funct_1(X4) )
           => ( ( r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
                & r1_tarski(X1,X0) )
             => ( m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
                & v1_funct_1(k2_partfun1(X0,X3,X4,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ~ v1_xboole_0(X3)
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
            & v1_funct_2(X4,X0,X3)
            & v1_funct_1(X4) )
         => ( ( r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
              & r1_tarski(X1,X0) )
           => ( m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
              & v1_funct_1(k2_partfun1(X0,X3,X4,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_funct_2)).

fof(f145,plain,(
    ! [X2] :
      ( k7_relat_1(sK4,X2) = k2_partfun1(sK0,sK3,sK4,X2)
      | ~ v1_funct_1(sK4) ) ),
    inference(resolution,[],[f52,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

% (16251)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f52,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(cnf_transformation,[],[f42])).

fof(f104,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl5_3
  <=> m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f206,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl5_12
  <=> m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f547,plain,
    ( spl5_2
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(avatar_contradiction_clause,[],[f546])).

fof(f546,plain,
    ( $false
    | spl5_2
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f545,f359])).

fof(f359,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_9
    | ~ spl5_13 ),
    inference(backward_demodulation,[],[f335,f357])).

fof(f357,plain,
    ( k1_xboole_0 = k9_relat_1(sK4,sK1)
    | ~ spl5_9
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f179,f211])).

fof(f211,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl5_13
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f179,plain,
    ( sK2 = k9_relat_1(sK4,sK1)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl5_9
  <=> sK2 = k9_relat_1(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f335,plain,
    ( m1_subset_1(k9_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_13 ),
    inference(backward_demodulation,[],[f171,f211])).

fof(f171,plain,(
    m1_subset_1(k9_relat_1(sK4,sK1),k1_zfmisc_1(sK2)) ),
    inference(resolution,[],[f158,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f158,plain,(
    r1_tarski(k9_relat_1(sK4,sK1),sK2) ),
    inference(backward_demodulation,[],[f54,f146])).

fof(f146,plain,(
    ! [X3] : k7_relset_1(sK0,sK3,sK4,X3) = k9_relat_1(sK4,X3) ),
    inference(resolution,[],[f52,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f54,plain,(
    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f545,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl5_2
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f544,f91])).

fof(f91,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f544,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl5_2
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f535,f498])).

fof(f498,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl5_2
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(backward_demodulation,[],[f449,f489])).

fof(f489,plain,
    ( k1_xboole_0 = sK1
    | spl5_2
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f488,f359])).

fof(f488,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK1
    | spl5_2
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f479,f91])).

fof(f479,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | spl5_2
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(resolution,[],[f448,f87])).

fof(f87,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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

fof(f448,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK1,k1_xboole_0)
    | spl5_2
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(backward_demodulation,[],[f337,f446])).

fof(f446,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,sK1)
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f436,f80])).

fof(f80,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f436,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,sK1)
    | ~ r1_tarski(k1_xboole_0,k7_relat_1(sK4,sK1))
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(resolution,[],[f354,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f354,plain,
    ( r1_tarski(k7_relat_1(sK4,sK1),k1_xboole_0)
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f346,f91])).

fof(f346,plain,
    ( r1_tarski(k7_relat_1(sK4,sK1),k2_zfmisc_1(sK1,k1_xboole_0))
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(backward_demodulation,[],[f300,f211])).

fof(f300,plain,
    ( r1_tarski(k7_relat_1(sK4,sK1),k2_zfmisc_1(sK1,sK2))
    | ~ spl5_12 ),
    inference(resolution,[],[f206,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f337,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,sK1),sK1,k1_xboole_0)
    | spl5_2
    | ~ spl5_13 ),
    inference(backward_demodulation,[],[f198,f211])).

fof(f198,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)
    | spl5_2 ),
    inference(forward_demodulation,[],[f100,f154])).

fof(f100,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl5_2
  <=> v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f449,plain,
    ( sK1 = k1_relset_1(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(backward_demodulation,[],[f339,f446])).

fof(f339,plain,
    ( sK1 = k1_relset_1(sK1,k1_xboole_0,k7_relat_1(sK4,sK1))
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(backward_demodulation,[],[f214,f211])).

fof(f214,plain,
    ( sK1 = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl5_14
  <=> sK1 = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f535,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl5_2
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(resolution,[],[f497,f89])).

fof(f89,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f497,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl5_2
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(backward_demodulation,[],[f448,f489])).

fof(f350,plain,
    ( spl5_8
    | ~ spl5_13 ),
    inference(avatar_contradiction_clause,[],[f349])).

fof(f349,plain,
    ( $false
    | spl5_8
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f336,f80])).

fof(f336,plain,
    ( ~ r1_tarski(k1_xboole_0,k9_relat_1(sK4,sK1))
    | spl5_8
    | ~ spl5_13 ),
    inference(backward_demodulation,[],[f175,f211])).

fof(f175,plain,
    ( ~ r1_tarski(sK2,k9_relat_1(sK4,sK1))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl5_8
  <=> r1_tarski(sK2,k9_relat_1(sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f332,plain,
    ( spl5_13
    | ~ spl5_14
    | spl5_2
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f331,f205,f98,f213,f209])).

fof(f331,plain,
    ( sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | k1_xboole_0 = sK2
    | spl5_2
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f297,f198])).

fof(f297,plain,
    ( v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)
    | sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | k1_xboole_0 = sK2
    | ~ spl5_12 ),
    inference(resolution,[],[f206,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f330,plain,
    ( ~ spl5_7
    | ~ spl5_12
    | spl5_14 ),
    inference(avatar_contradiction_clause,[],[f329])).

fof(f329,plain,
    ( $false
    | ~ spl5_7
    | ~ spl5_12
    | spl5_14 ),
    inference(subsumption_resolution,[],[f328,f53])).

fof(f53,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f328,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ spl5_7
    | ~ spl5_12
    | spl5_14 ),
    inference(forward_demodulation,[],[f327,f159])).

fof(f159,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f149,f131])).

fof(f131,plain,
    ( sK0 = k1_relset_1(sK0,sK3,sK4)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl5_7
  <=> sK0 = k1_relset_1(sK0,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f149,plain,(
    k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4) ),
    inference(resolution,[],[f52,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f327,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(sK4))
    | ~ spl5_12
    | spl5_14 ),
    inference(subsumption_resolution,[],[f326,f160])).

fof(f160,plain,(
    v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f150,f81])).

fof(f81,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f150,plain,
    ( v1_relat_1(sK4)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK3)) ),
    inference(resolution,[],[f52,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

% (16227)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f326,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ spl5_12
    | spl5_14 ),
    inference(trivial_inequality_removal,[],[f325])).

fof(f325,plain,
    ( sK1 != sK1
    | ~ r1_tarski(sK1,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ spl5_12
    | spl5_14 ),
    inference(superposition,[],[f310,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

% (16252)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f310,plain,
    ( sK1 != k1_relat_1(k7_relat_1(sK4,sK1))
    | ~ spl5_12
    | spl5_14 ),
    inference(subsumption_resolution,[],[f307,f206])).

fof(f307,plain,
    ( sK1 != k1_relat_1(k7_relat_1(sK4,sK1))
    | ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl5_14 ),
    inference(superposition,[],[f215,f76])).

fof(f215,plain,
    ( sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | spl5_14 ),
    inference(avatar_component_clause,[],[f213])).

% (16236)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
fof(f289,plain,(
    spl5_12 ),
    inference(avatar_contradiction_clause,[],[f288])).

fof(f288,plain,
    ( $false
    | spl5_12 ),
    inference(subsumption_resolution,[],[f287,f158])).

fof(f287,plain,
    ( ~ r1_tarski(k9_relat_1(sK4,sK1),sK2)
    | spl5_12 ),
    inference(forward_demodulation,[],[f286,f163])).

fof(f163,plain,(
    ! [X3] : k9_relat_1(sK4,X3) = k2_relat_1(k7_relat_1(sK4,X3)) ),
    inference(resolution,[],[f160,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f286,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2)
    | spl5_12 ),
    inference(subsumption_resolution,[],[f285,f164])).

fof(f164,plain,(
    ! [X4] : v1_relat_1(k7_relat_1(sK4,X4)) ),
    inference(resolution,[],[f160,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

% (16244)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f285,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2)
    | ~ v1_relat_1(k7_relat_1(sK4,sK1))
    | spl5_12 ),
    inference(subsumption_resolution,[],[f283,f165])).

fof(f165,plain,(
    ! [X5] : r1_tarski(k1_relat_1(k7_relat_1(sK4,X5)),X5) ),
    inference(resolution,[],[f160,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f283,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1)
    | ~ v1_relat_1(k7_relat_1(sK4,sK1))
    | spl5_12 ),
    inference(resolution,[],[f207,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f207,plain,
    ( ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f205])).

fof(f197,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f193])).

fof(f193,plain,
    ( $false
    | spl5_1 ),
    inference(resolution,[],[f157,f155])).

fof(f155,plain,
    ( ~ v1_funct_1(k7_relat_1(sK4,sK1))
    | spl5_1 ),
    inference(backward_demodulation,[],[f96,f154])).

fof(f96,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl5_1
  <=> v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f157,plain,(
    ! [X0] : v1_funct_1(k7_relat_1(sK4,X0)) ),
    inference(backward_demodulation,[],[f152,f154])).

fof(f152,plain,(
    ! [X0] : v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0)) ),
    inference(subsumption_resolution,[],[f143,f50])).

fof(f143,plain,(
    ! [X0] :
      ( v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0))
      | ~ v1_funct_1(sK4) ) ),
    inference(resolution,[],[f52,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f181,plain,
    ( ~ spl5_8
    | spl5_9 ),
    inference(avatar_split_clause,[],[f170,f177,f173])).

fof(f170,plain,
    ( sK2 = k9_relat_1(sK4,sK1)
    | ~ r1_tarski(sK2,k9_relat_1(sK4,sK1)) ),
    inference(resolution,[],[f158,f64])).

fof(f139,plain,(
    ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f138])).

fof(f138,plain,
    ( $false
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f134,f71])).

fof(f71,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f134,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl5_6 ),
    inference(backward_demodulation,[],[f49,f127])).

fof(f127,plain,
    ( k1_xboole_0 = sK3
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl5_6
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f49,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f132,plain,
    ( spl5_6
    | spl5_7 ),
    inference(avatar_split_clause,[],[f123,f129,f125])).

fof(f123,plain,
    ( sK0 = k1_relset_1(sK0,sK3,sK4)
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f122,f52])).

fof(f122,plain,
    ( sK0 = k1_relset_1(sK0,sK3,sK4)
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(resolution,[],[f51,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f51,plain,(
    v1_funct_2(sK4,sK0,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f105,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f55,f102,f98,f94])).

fof(f55,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:14:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.56  % (16230)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.57  % (16231)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.57  % (16233)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.57  % (16234)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.57  % (16237)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.57  % (16250)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.57  % (16229)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.59/0.58  % (16245)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.59/0.58  % (16238)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.59/0.58  % (16246)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.59/0.58  % (16242)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.59/0.58  % (16249)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.59/0.58  % (16247)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.59/0.58  % (16232)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.59/0.58  % (16241)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.59/0.59  % (16239)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.59/0.60  % (16240)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.78/0.60  % (16248)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.78/0.62  % (16238)Refutation found. Thanks to Tanya!
% 1.78/0.62  % SZS status Theorem for theBenchmark
% 1.78/0.63  % SZS output start Proof for theBenchmark
% 1.78/0.63  fof(f571,plain,(
% 1.78/0.63    $false),
% 1.78/0.63    inference(avatar_sat_refutation,[],[f105,f132,f139,f181,f197,f289,f330,f332,f350,f547,f568])).
% 1.78/0.63  fof(f568,plain,(
% 1.78/0.63    spl5_3 | ~spl5_12),
% 1.78/0.63    inference(avatar_contradiction_clause,[],[f567])).
% 1.78/0.63  fof(f567,plain,(
% 1.78/0.63    $false | (spl5_3 | ~spl5_12)),
% 1.78/0.63    inference(subsumption_resolution,[],[f206,f562])).
% 1.78/0.63  fof(f562,plain,(
% 1.78/0.63    ~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl5_3),
% 1.78/0.63    inference(forward_demodulation,[],[f104,f154])).
% 1.78/0.63  fof(f154,plain,(
% 1.78/0.63    ( ! [X2] : (k7_relat_1(sK4,X2) = k2_partfun1(sK0,sK3,sK4,X2)) )),
% 1.78/0.63    inference(subsumption_resolution,[],[f145,f50])).
% 1.78/0.63  fof(f50,plain,(
% 1.78/0.63    v1_funct_1(sK4)),
% 1.78/0.63    inference(cnf_transformation,[],[f42])).
% 1.78/0.63  fof(f42,plain,(
% 1.78/0.63    ((~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))) & r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) & r1_tarski(sK1,sK0) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) & v1_funct_2(sK4,sK0,sK3) & v1_funct_1(sK4)) & ~v1_xboole_0(sK3)),
% 1.78/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f23,f41,f40])).
% 1.78/0.63  fof(f40,plain,(
% 1.78/0.63    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3)) => (? [X4] : ((~m1_subset_1(k2_partfun1(sK0,sK3,X4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,X4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,X4,sK1))) & r1_tarski(k7_relset_1(sK0,sK3,X4,sK1),sK2) & r1_tarski(sK1,sK0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) & v1_funct_2(X4,sK0,sK3) & v1_funct_1(X4)) & ~v1_xboole_0(sK3))),
% 1.78/0.63    introduced(choice_axiom,[])).
% 1.78/0.63  fof(f41,plain,(
% 1.78/0.63    ? [X4] : ((~m1_subset_1(k2_partfun1(sK0,sK3,X4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,X4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,X4,sK1))) & r1_tarski(k7_relset_1(sK0,sK3,X4,sK1),sK2) & r1_tarski(sK1,sK0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) & v1_funct_2(X4,sK0,sK3) & v1_funct_1(X4)) => ((~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))) & r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) & r1_tarski(sK1,sK0) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) & v1_funct_2(sK4,sK0,sK3) & v1_funct_1(sK4))),
% 1.78/0.63    introduced(choice_axiom,[])).
% 1.78/0.63  fof(f23,plain,(
% 1.78/0.63    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3))),
% 1.78/0.63    inference(flattening,[],[f22])).
% 1.78/0.63  fof(f22,plain,(
% 1.78/0.63    ? [X0,X1,X2,X3] : (? [X4] : (((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & (r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4))) & ~v1_xboole_0(X3))),
% 1.78/0.63    inference(ennf_transformation,[],[f21])).
% 1.78/0.63  fof(f21,negated_conjecture,(
% 1.78/0.63    ~! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 1.78/0.63    inference(negated_conjecture,[],[f20])).
% 1.78/0.63  fof(f20,conjecture,(
% 1.78/0.63    ! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 1.78/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_funct_2)).
% 1.78/0.63  fof(f145,plain,(
% 1.78/0.63    ( ! [X2] : (k7_relat_1(sK4,X2) = k2_partfun1(sK0,sK3,sK4,X2) | ~v1_funct_1(sK4)) )),
% 1.78/0.63    inference(resolution,[],[f52,f58])).
% 1.78/0.63  fof(f58,plain,(
% 1.78/0.63    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.78/0.63    inference(cnf_transformation,[],[f27])).
% 1.78/0.63  % (16251)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.78/0.63  fof(f27,plain,(
% 1.78/0.63    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.78/0.63    inference(flattening,[],[f26])).
% 1.78/0.63  fof(f26,plain,(
% 1.78/0.63    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.78/0.63    inference(ennf_transformation,[],[f19])).
% 1.78/0.63  fof(f19,axiom,(
% 1.78/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.78/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.78/0.63  fof(f52,plain,(
% 1.78/0.63    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 1.78/0.63    inference(cnf_transformation,[],[f42])).
% 1.78/0.63  fof(f104,plain,(
% 1.78/0.63    ~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl5_3),
% 1.78/0.63    inference(avatar_component_clause,[],[f102])).
% 1.78/0.63  fof(f102,plain,(
% 1.78/0.63    spl5_3 <=> m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.78/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.78/0.63  fof(f206,plain,(
% 1.78/0.63    m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_12),
% 1.78/0.63    inference(avatar_component_clause,[],[f205])).
% 1.78/0.63  fof(f205,plain,(
% 1.78/0.63    spl5_12 <=> m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.78/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.78/0.63  fof(f547,plain,(
% 1.78/0.63    spl5_2 | ~spl5_9 | ~spl5_12 | ~spl5_13 | ~spl5_14),
% 1.78/0.63    inference(avatar_contradiction_clause,[],[f546])).
% 1.78/0.63  fof(f546,plain,(
% 1.78/0.63    $false | (spl5_2 | ~spl5_9 | ~spl5_12 | ~spl5_13 | ~spl5_14)),
% 1.78/0.63    inference(subsumption_resolution,[],[f545,f359])).
% 1.78/0.63  fof(f359,plain,(
% 1.78/0.63    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl5_9 | ~spl5_13)),
% 1.78/0.63    inference(backward_demodulation,[],[f335,f357])).
% 1.78/0.63  fof(f357,plain,(
% 1.78/0.63    k1_xboole_0 = k9_relat_1(sK4,sK1) | (~spl5_9 | ~spl5_13)),
% 1.78/0.63    inference(forward_demodulation,[],[f179,f211])).
% 1.78/0.63  fof(f211,plain,(
% 1.78/0.63    k1_xboole_0 = sK2 | ~spl5_13),
% 1.78/0.63    inference(avatar_component_clause,[],[f209])).
% 1.78/0.63  fof(f209,plain,(
% 1.78/0.63    spl5_13 <=> k1_xboole_0 = sK2),
% 1.78/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.78/0.63  fof(f179,plain,(
% 1.78/0.63    sK2 = k9_relat_1(sK4,sK1) | ~spl5_9),
% 1.78/0.63    inference(avatar_component_clause,[],[f177])).
% 1.78/0.63  fof(f177,plain,(
% 1.78/0.63    spl5_9 <=> sK2 = k9_relat_1(sK4,sK1)),
% 1.78/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.78/0.63  fof(f335,plain,(
% 1.78/0.63    m1_subset_1(k9_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0)) | ~spl5_13),
% 1.78/0.63    inference(backward_demodulation,[],[f171,f211])).
% 1.78/0.63  fof(f171,plain,(
% 1.78/0.63    m1_subset_1(k9_relat_1(sK4,sK1),k1_zfmisc_1(sK2))),
% 1.78/0.63    inference(resolution,[],[f158,f61])).
% 1.78/0.63  fof(f61,plain,(
% 1.78/0.63    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.78/0.63    inference(cnf_transformation,[],[f43])).
% 1.78/0.63  fof(f43,plain,(
% 1.78/0.63    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.78/0.63    inference(nnf_transformation,[],[f5])).
% 1.78/0.63  fof(f5,axiom,(
% 1.78/0.63    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.78/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.78/0.63  fof(f158,plain,(
% 1.78/0.63    r1_tarski(k9_relat_1(sK4,sK1),sK2)),
% 1.78/0.63    inference(backward_demodulation,[],[f54,f146])).
% 1.78/0.63  fof(f146,plain,(
% 1.78/0.63    ( ! [X3] : (k7_relset_1(sK0,sK3,sK4,X3) = k9_relat_1(sK4,X3)) )),
% 1.78/0.63    inference(resolution,[],[f52,f59])).
% 1.78/0.63  fof(f59,plain,(
% 1.78/0.63    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.78/0.63    inference(cnf_transformation,[],[f28])).
% 1.78/0.63  fof(f28,plain,(
% 1.78/0.63    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.78/0.63    inference(ennf_transformation,[],[f15])).
% 1.78/0.63  fof(f15,axiom,(
% 1.78/0.63    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.78/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.78/0.63  fof(f54,plain,(
% 1.78/0.63    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)),
% 1.78/0.63    inference(cnf_transformation,[],[f42])).
% 1.78/0.63  fof(f545,plain,(
% 1.78/0.63    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (spl5_2 | ~spl5_9 | ~spl5_12 | ~spl5_13 | ~spl5_14)),
% 1.78/0.63    inference(forward_demodulation,[],[f544,f91])).
% 1.78/0.63  fof(f91,plain,(
% 1.78/0.63    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.78/0.63    inference(equality_resolution,[],[f79])).
% 1.78/0.63  fof(f79,plain,(
% 1.78/0.63    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.78/0.63    inference(cnf_transformation,[],[f48])).
% 1.78/0.63  fof(f48,plain,(
% 1.78/0.63    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.78/0.63    inference(flattening,[],[f47])).
% 1.78/0.63  fof(f47,plain,(
% 1.78/0.63    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.78/0.63    inference(nnf_transformation,[],[f4])).
% 1.78/0.63  fof(f4,axiom,(
% 1.78/0.63    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.78/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.78/0.63  fof(f544,plain,(
% 1.78/0.63    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (spl5_2 | ~spl5_9 | ~spl5_12 | ~spl5_13 | ~spl5_14)),
% 1.78/0.63    inference(subsumption_resolution,[],[f535,f498])).
% 1.78/0.63  fof(f498,plain,(
% 1.78/0.63    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl5_2 | ~spl5_9 | ~spl5_12 | ~spl5_13 | ~spl5_14)),
% 1.78/0.63    inference(backward_demodulation,[],[f449,f489])).
% 1.78/0.63  fof(f489,plain,(
% 1.78/0.63    k1_xboole_0 = sK1 | (spl5_2 | ~spl5_9 | ~spl5_12 | ~spl5_13)),
% 1.78/0.63    inference(subsumption_resolution,[],[f488,f359])).
% 1.78/0.63  fof(f488,plain,(
% 1.78/0.63    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK1 | (spl5_2 | ~spl5_12 | ~spl5_13)),
% 1.78/0.63    inference(forward_demodulation,[],[f479,f91])).
% 1.78/0.63  fof(f479,plain,(
% 1.78/0.63    k1_xboole_0 = sK1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) | (spl5_2 | ~spl5_12 | ~spl5_13)),
% 1.78/0.63    inference(resolution,[],[f448,f87])).
% 1.78/0.63  fof(f87,plain,(
% 1.78/0.63    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 1.78/0.63    inference(equality_resolution,[],[f86])).
% 1.78/0.63  fof(f86,plain,(
% 1.78/0.63    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.78/0.63    inference(equality_resolution,[],[f70])).
% 1.78/0.63  fof(f70,plain,(
% 1.78/0.63    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.78/0.63    inference(cnf_transformation,[],[f46])).
% 1.78/0.63  fof(f46,plain,(
% 1.78/0.63    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.78/0.63    inference(nnf_transformation,[],[f30])).
% 1.78/0.63  fof(f30,plain,(
% 1.78/0.63    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.78/0.63    inference(flattening,[],[f29])).
% 1.78/0.63  fof(f29,plain,(
% 1.78/0.63    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.78/0.63    inference(ennf_transformation,[],[f17])).
% 1.78/0.63  fof(f17,axiom,(
% 1.78/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.78/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.78/0.63  fof(f448,plain,(
% 1.78/0.63    ~v1_funct_2(k1_xboole_0,sK1,k1_xboole_0) | (spl5_2 | ~spl5_12 | ~spl5_13)),
% 1.78/0.63    inference(backward_demodulation,[],[f337,f446])).
% 1.78/0.63  fof(f446,plain,(
% 1.78/0.63    k1_xboole_0 = k7_relat_1(sK4,sK1) | (~spl5_12 | ~spl5_13)),
% 1.78/0.63    inference(subsumption_resolution,[],[f436,f80])).
% 1.78/0.63  fof(f80,plain,(
% 1.78/0.63    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.78/0.63    inference(cnf_transformation,[],[f3])).
% 1.78/0.63  fof(f3,axiom,(
% 1.78/0.63    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.78/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.78/0.63  fof(f436,plain,(
% 1.78/0.63    k1_xboole_0 = k7_relat_1(sK4,sK1) | ~r1_tarski(k1_xboole_0,k7_relat_1(sK4,sK1)) | (~spl5_12 | ~spl5_13)),
% 1.78/0.63    inference(resolution,[],[f354,f64])).
% 1.78/0.63  fof(f64,plain,(
% 1.78/0.63    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.78/0.63    inference(cnf_transformation,[],[f45])).
% 1.78/0.63  fof(f45,plain,(
% 1.78/0.63    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.78/0.63    inference(flattening,[],[f44])).
% 1.78/0.63  fof(f44,plain,(
% 1.78/0.63    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.78/0.63    inference(nnf_transformation,[],[f2])).
% 1.78/0.63  fof(f2,axiom,(
% 1.78/0.63    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.78/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.78/0.63  fof(f354,plain,(
% 1.78/0.63    r1_tarski(k7_relat_1(sK4,sK1),k1_xboole_0) | (~spl5_12 | ~spl5_13)),
% 1.78/0.63    inference(forward_demodulation,[],[f346,f91])).
% 1.78/0.63  fof(f346,plain,(
% 1.78/0.63    r1_tarski(k7_relat_1(sK4,sK1),k2_zfmisc_1(sK1,k1_xboole_0)) | (~spl5_12 | ~spl5_13)),
% 1.78/0.63    inference(backward_demodulation,[],[f300,f211])).
% 1.78/0.63  fof(f300,plain,(
% 1.78/0.63    r1_tarski(k7_relat_1(sK4,sK1),k2_zfmisc_1(sK1,sK2)) | ~spl5_12),
% 1.78/0.63    inference(resolution,[],[f206,f60])).
% 1.78/0.63  fof(f60,plain,(
% 1.78/0.63    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.78/0.63    inference(cnf_transformation,[],[f43])).
% 1.78/0.63  fof(f337,plain,(
% 1.78/0.63    ~v1_funct_2(k7_relat_1(sK4,sK1),sK1,k1_xboole_0) | (spl5_2 | ~spl5_13)),
% 1.78/0.63    inference(backward_demodulation,[],[f198,f211])).
% 1.78/0.63  fof(f198,plain,(
% 1.78/0.63    ~v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) | spl5_2),
% 1.78/0.63    inference(forward_demodulation,[],[f100,f154])).
% 1.78/0.63  fof(f100,plain,(
% 1.78/0.63    ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | spl5_2),
% 1.78/0.63    inference(avatar_component_clause,[],[f98])).
% 1.78/0.63  fof(f98,plain,(
% 1.78/0.63    spl5_2 <=> v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)),
% 1.78/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.78/0.63  fof(f449,plain,(
% 1.78/0.63    sK1 = k1_relset_1(sK1,k1_xboole_0,k1_xboole_0) | (~spl5_12 | ~spl5_13 | ~spl5_14)),
% 1.78/0.63    inference(backward_demodulation,[],[f339,f446])).
% 1.78/0.63  fof(f339,plain,(
% 1.78/0.63    sK1 = k1_relset_1(sK1,k1_xboole_0,k7_relat_1(sK4,sK1)) | (~spl5_13 | ~spl5_14)),
% 1.78/0.63    inference(backward_demodulation,[],[f214,f211])).
% 1.78/0.63  fof(f214,plain,(
% 1.78/0.63    sK1 = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | ~spl5_14),
% 1.78/0.63    inference(avatar_component_clause,[],[f213])).
% 1.78/0.63  fof(f213,plain,(
% 1.78/0.63    spl5_14 <=> sK1 = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))),
% 1.78/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.78/0.63  fof(f535,plain,(
% 1.78/0.63    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (spl5_2 | ~spl5_9 | ~spl5_12 | ~spl5_13)),
% 1.78/0.63    inference(resolution,[],[f497,f89])).
% 1.78/0.63  fof(f89,plain,(
% 1.78/0.63    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.78/0.63    inference(equality_resolution,[],[f68])).
% 1.78/0.63  fof(f68,plain,(
% 1.78/0.63    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.78/0.63    inference(cnf_transformation,[],[f46])).
% 1.78/0.63  fof(f497,plain,(
% 1.78/0.63    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl5_2 | ~spl5_9 | ~spl5_12 | ~spl5_13)),
% 1.78/0.63    inference(backward_demodulation,[],[f448,f489])).
% 1.78/0.63  fof(f350,plain,(
% 1.78/0.63    spl5_8 | ~spl5_13),
% 1.78/0.63    inference(avatar_contradiction_clause,[],[f349])).
% 1.78/0.63  fof(f349,plain,(
% 1.78/0.63    $false | (spl5_8 | ~spl5_13)),
% 1.78/0.63    inference(subsumption_resolution,[],[f336,f80])).
% 1.78/0.63  fof(f336,plain,(
% 1.78/0.63    ~r1_tarski(k1_xboole_0,k9_relat_1(sK4,sK1)) | (spl5_8 | ~spl5_13)),
% 1.78/0.63    inference(backward_demodulation,[],[f175,f211])).
% 1.78/0.63  fof(f175,plain,(
% 1.78/0.63    ~r1_tarski(sK2,k9_relat_1(sK4,sK1)) | spl5_8),
% 1.78/0.63    inference(avatar_component_clause,[],[f173])).
% 1.78/0.63  fof(f173,plain,(
% 1.78/0.63    spl5_8 <=> r1_tarski(sK2,k9_relat_1(sK4,sK1))),
% 1.78/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.78/0.63  fof(f332,plain,(
% 1.78/0.63    spl5_13 | ~spl5_14 | spl5_2 | ~spl5_12),
% 1.78/0.63    inference(avatar_split_clause,[],[f331,f205,f98,f213,f209])).
% 1.78/0.63  fof(f331,plain,(
% 1.78/0.63    sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | k1_xboole_0 = sK2 | (spl5_2 | ~spl5_12)),
% 1.78/0.63    inference(subsumption_resolution,[],[f297,f198])).
% 1.78/0.63  fof(f297,plain,(
% 1.78/0.63    v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) | sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | k1_xboole_0 = sK2 | ~spl5_12),
% 1.78/0.63    inference(resolution,[],[f206,f67])).
% 1.78/0.63  fof(f67,plain,(
% 1.78/0.63    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.78/0.63    inference(cnf_transformation,[],[f46])).
% 1.78/0.63  fof(f330,plain,(
% 1.78/0.63    ~spl5_7 | ~spl5_12 | spl5_14),
% 1.78/0.63    inference(avatar_contradiction_clause,[],[f329])).
% 1.78/0.63  fof(f329,plain,(
% 1.78/0.63    $false | (~spl5_7 | ~spl5_12 | spl5_14)),
% 1.78/0.63    inference(subsumption_resolution,[],[f328,f53])).
% 1.78/0.63  fof(f53,plain,(
% 1.78/0.63    r1_tarski(sK1,sK0)),
% 1.78/0.63    inference(cnf_transformation,[],[f42])).
% 1.78/0.63  fof(f328,plain,(
% 1.78/0.63    ~r1_tarski(sK1,sK0) | (~spl5_7 | ~spl5_12 | spl5_14)),
% 1.78/0.63    inference(forward_demodulation,[],[f327,f159])).
% 1.78/0.63  fof(f159,plain,(
% 1.78/0.63    sK0 = k1_relat_1(sK4) | ~spl5_7),
% 1.78/0.63    inference(forward_demodulation,[],[f149,f131])).
% 1.78/0.63  fof(f131,plain,(
% 1.78/0.63    sK0 = k1_relset_1(sK0,sK3,sK4) | ~spl5_7),
% 1.78/0.63    inference(avatar_component_clause,[],[f129])).
% 1.78/0.63  fof(f129,plain,(
% 1.78/0.63    spl5_7 <=> sK0 = k1_relset_1(sK0,sK3,sK4)),
% 1.78/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.78/0.63  fof(f149,plain,(
% 1.78/0.63    k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4)),
% 1.78/0.63    inference(resolution,[],[f52,f76])).
% 1.78/0.63  fof(f76,plain,(
% 1.78/0.63    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.78/0.63    inference(cnf_transformation,[],[f36])).
% 1.78/0.63  fof(f36,plain,(
% 1.78/0.63    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.78/0.63    inference(ennf_transformation,[],[f14])).
% 1.78/0.63  fof(f14,axiom,(
% 1.78/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.78/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.78/0.63  fof(f327,plain,(
% 1.78/0.63    ~r1_tarski(sK1,k1_relat_1(sK4)) | (~spl5_12 | spl5_14)),
% 1.78/0.63    inference(subsumption_resolution,[],[f326,f160])).
% 1.78/0.63  fof(f160,plain,(
% 1.78/0.63    v1_relat_1(sK4)),
% 1.78/0.63    inference(subsumption_resolution,[],[f150,f81])).
% 1.78/0.63  fof(f81,plain,(
% 1.78/0.63    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.78/0.63    inference(cnf_transformation,[],[f9])).
% 1.78/0.63  fof(f9,axiom,(
% 1.78/0.63    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.78/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.78/0.63  fof(f150,plain,(
% 1.78/0.63    v1_relat_1(sK4) | ~v1_relat_1(k2_zfmisc_1(sK0,sK3))),
% 1.78/0.63    inference(resolution,[],[f52,f82])).
% 1.78/0.63  fof(f82,plain,(
% 1.78/0.63    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.78/0.63    inference(cnf_transformation,[],[f37])).
% 1.78/0.63  % (16227)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.78/0.63  fof(f37,plain,(
% 1.78/0.63    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.78/0.63    inference(ennf_transformation,[],[f6])).
% 1.78/0.63  fof(f6,axiom,(
% 1.78/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.78/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.78/0.63  fof(f326,plain,(
% 1.78/0.63    ~r1_tarski(sK1,k1_relat_1(sK4)) | ~v1_relat_1(sK4) | (~spl5_12 | spl5_14)),
% 1.78/0.63    inference(trivial_inequality_removal,[],[f325])).
% 1.78/0.63  fof(f325,plain,(
% 1.78/0.63    sK1 != sK1 | ~r1_tarski(sK1,k1_relat_1(sK4)) | ~v1_relat_1(sK4) | (~spl5_12 | spl5_14)),
% 1.78/0.63    inference(superposition,[],[f310,f72])).
% 1.78/0.63  fof(f72,plain,(
% 1.78/0.63    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.78/0.63    inference(cnf_transformation,[],[f32])).
% 1.78/0.63  fof(f32,plain,(
% 1.78/0.63    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.78/0.63    inference(flattening,[],[f31])).
% 1.78/0.63  fof(f31,plain,(
% 1.78/0.63    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.78/0.63    inference(ennf_transformation,[],[f12])).
% 1.78/0.63  % (16252)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.78/0.63  fof(f12,axiom,(
% 1.78/0.63    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.78/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 1.78/0.63  fof(f310,plain,(
% 1.78/0.63    sK1 != k1_relat_1(k7_relat_1(sK4,sK1)) | (~spl5_12 | spl5_14)),
% 1.78/0.63    inference(subsumption_resolution,[],[f307,f206])).
% 1.78/0.63  fof(f307,plain,(
% 1.78/0.63    sK1 != k1_relat_1(k7_relat_1(sK4,sK1)) | ~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl5_14),
% 1.78/0.63    inference(superposition,[],[f215,f76])).
% 1.78/0.63  fof(f215,plain,(
% 1.78/0.63    sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | spl5_14),
% 1.78/0.63    inference(avatar_component_clause,[],[f213])).
% 1.78/0.64  % (16236)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.78/0.64  fof(f289,plain,(
% 1.78/0.64    spl5_12),
% 1.78/0.64    inference(avatar_contradiction_clause,[],[f288])).
% 1.78/0.64  fof(f288,plain,(
% 1.78/0.64    $false | spl5_12),
% 1.78/0.64    inference(subsumption_resolution,[],[f287,f158])).
% 1.78/0.64  fof(f287,plain,(
% 1.78/0.64    ~r1_tarski(k9_relat_1(sK4,sK1),sK2) | spl5_12),
% 1.78/0.64    inference(forward_demodulation,[],[f286,f163])).
% 1.78/0.64  fof(f163,plain,(
% 1.78/0.64    ( ! [X3] : (k9_relat_1(sK4,X3) = k2_relat_1(k7_relat_1(sK4,X3))) )),
% 1.78/0.64    inference(resolution,[],[f160,f75])).
% 1.78/0.64  fof(f75,plain,(
% 1.78/0.64    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.78/0.64    inference(cnf_transformation,[],[f35])).
% 1.78/0.64  fof(f35,plain,(
% 1.78/0.64    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.78/0.64    inference(ennf_transformation,[],[f10])).
% 1.78/0.64  fof(f10,axiom,(
% 1.78/0.64    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.78/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 1.78/0.64  fof(f286,plain,(
% 1.78/0.64    ~r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) | spl5_12),
% 1.78/0.64    inference(subsumption_resolution,[],[f285,f164])).
% 1.78/0.64  fof(f164,plain,(
% 1.78/0.64    ( ! [X4] : (v1_relat_1(k7_relat_1(sK4,X4))) )),
% 1.78/0.64    inference(resolution,[],[f160,f74])).
% 1.78/0.64  fof(f74,plain,(
% 1.78/0.64    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.78/0.64    inference(cnf_transformation,[],[f34])).
% 1.78/0.64  % (16244)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.78/0.64  fof(f34,plain,(
% 1.78/0.64    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.78/0.64    inference(ennf_transformation,[],[f8])).
% 1.78/0.64  fof(f8,axiom,(
% 1.78/0.64    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.78/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.78/0.64  fof(f285,plain,(
% 1.78/0.64    ~r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) | ~v1_relat_1(k7_relat_1(sK4,sK1)) | spl5_12),
% 1.78/0.64    inference(subsumption_resolution,[],[f283,f165])).
% 1.78/0.64  fof(f165,plain,(
% 1.78/0.64    ( ! [X5] : (r1_tarski(k1_relat_1(k7_relat_1(sK4,X5)),X5)) )),
% 1.78/0.64    inference(resolution,[],[f160,f73])).
% 1.78/0.64  fof(f73,plain,(
% 1.78/0.64    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 1.78/0.64    inference(cnf_transformation,[],[f33])).
% 1.78/0.64  fof(f33,plain,(
% 1.78/0.64    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 1.78/0.64    inference(ennf_transformation,[],[f11])).
% 1.78/0.64  fof(f11,axiom,(
% 1.78/0.64    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 1.78/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 1.78/0.64  fof(f283,plain,(
% 1.78/0.64    ~r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) | ~r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) | ~v1_relat_1(k7_relat_1(sK4,sK1)) | spl5_12),
% 1.78/0.64    inference(resolution,[],[f207,f83])).
% 1.78/0.64  fof(f83,plain,(
% 1.78/0.64    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 1.78/0.64    inference(cnf_transformation,[],[f39])).
% 1.78/0.64  fof(f39,plain,(
% 1.78/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.78/0.64    inference(flattening,[],[f38])).
% 1.78/0.64  fof(f38,plain,(
% 1.78/0.64    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.78/0.64    inference(ennf_transformation,[],[f16])).
% 1.78/0.64  fof(f16,axiom,(
% 1.78/0.64    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.78/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 1.78/0.64  fof(f207,plain,(
% 1.78/0.64    ~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl5_12),
% 1.78/0.64    inference(avatar_component_clause,[],[f205])).
% 1.78/0.64  fof(f197,plain,(
% 1.78/0.64    spl5_1),
% 1.78/0.64    inference(avatar_contradiction_clause,[],[f193])).
% 1.78/0.64  fof(f193,plain,(
% 1.78/0.64    $false | spl5_1),
% 1.78/0.64    inference(resolution,[],[f157,f155])).
% 1.78/0.64  fof(f155,plain,(
% 1.78/0.64    ~v1_funct_1(k7_relat_1(sK4,sK1)) | spl5_1),
% 1.78/0.64    inference(backward_demodulation,[],[f96,f154])).
% 1.78/0.64  fof(f96,plain,(
% 1.78/0.64    ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) | spl5_1),
% 1.78/0.64    inference(avatar_component_clause,[],[f94])).
% 1.78/0.64  fof(f94,plain,(
% 1.78/0.64    spl5_1 <=> v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))),
% 1.78/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.78/0.64  fof(f157,plain,(
% 1.78/0.64    ( ! [X0] : (v1_funct_1(k7_relat_1(sK4,X0))) )),
% 1.78/0.64    inference(backward_demodulation,[],[f152,f154])).
% 1.78/0.64  fof(f152,plain,(
% 1.78/0.64    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0))) )),
% 1.78/0.64    inference(subsumption_resolution,[],[f143,f50])).
% 1.78/0.64  fof(f143,plain,(
% 1.78/0.64    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0)) | ~v1_funct_1(sK4)) )),
% 1.78/0.64    inference(resolution,[],[f52,f56])).
% 1.78/0.64  fof(f56,plain,(
% 1.78/0.64    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.78/0.64    inference(cnf_transformation,[],[f25])).
% 1.78/0.64  fof(f25,plain,(
% 1.78/0.64    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.78/0.64    inference(flattening,[],[f24])).
% 1.78/0.64  fof(f24,plain,(
% 1.78/0.64    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.78/0.64    inference(ennf_transformation,[],[f18])).
% 1.78/0.64  fof(f18,axiom,(
% 1.78/0.64    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 1.78/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 1.78/0.64  fof(f181,plain,(
% 1.78/0.64    ~spl5_8 | spl5_9),
% 1.78/0.64    inference(avatar_split_clause,[],[f170,f177,f173])).
% 1.78/0.64  fof(f170,plain,(
% 1.78/0.64    sK2 = k9_relat_1(sK4,sK1) | ~r1_tarski(sK2,k9_relat_1(sK4,sK1))),
% 1.78/0.64    inference(resolution,[],[f158,f64])).
% 1.78/0.64  fof(f139,plain,(
% 1.78/0.64    ~spl5_6),
% 1.78/0.64    inference(avatar_contradiction_clause,[],[f138])).
% 1.78/0.64  fof(f138,plain,(
% 1.78/0.64    $false | ~spl5_6),
% 1.78/0.64    inference(subsumption_resolution,[],[f134,f71])).
% 1.78/0.64  fof(f71,plain,(
% 1.78/0.64    v1_xboole_0(k1_xboole_0)),
% 1.78/0.64    inference(cnf_transformation,[],[f1])).
% 1.78/0.64  fof(f1,axiom,(
% 1.78/0.64    v1_xboole_0(k1_xboole_0)),
% 1.78/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.78/0.64  fof(f134,plain,(
% 1.78/0.64    ~v1_xboole_0(k1_xboole_0) | ~spl5_6),
% 1.78/0.64    inference(backward_demodulation,[],[f49,f127])).
% 1.78/0.64  fof(f127,plain,(
% 1.78/0.64    k1_xboole_0 = sK3 | ~spl5_6),
% 1.78/0.64    inference(avatar_component_clause,[],[f125])).
% 1.78/0.64  fof(f125,plain,(
% 1.78/0.64    spl5_6 <=> k1_xboole_0 = sK3),
% 1.78/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.78/0.64  fof(f49,plain,(
% 1.78/0.64    ~v1_xboole_0(sK3)),
% 1.78/0.64    inference(cnf_transformation,[],[f42])).
% 1.78/0.64  fof(f132,plain,(
% 1.78/0.64    spl5_6 | spl5_7),
% 1.78/0.64    inference(avatar_split_clause,[],[f123,f129,f125])).
% 1.78/0.64  fof(f123,plain,(
% 1.78/0.64    sK0 = k1_relset_1(sK0,sK3,sK4) | k1_xboole_0 = sK3),
% 1.78/0.64    inference(subsumption_resolution,[],[f122,f52])).
% 1.78/0.64  fof(f122,plain,(
% 1.78/0.64    sK0 = k1_relset_1(sK0,sK3,sK4) | k1_xboole_0 = sK3 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 1.78/0.64    inference(resolution,[],[f51,f65])).
% 1.78/0.64  fof(f65,plain,(
% 1.78/0.64    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.78/0.64    inference(cnf_transformation,[],[f46])).
% 1.78/0.64  fof(f51,plain,(
% 1.78/0.64    v1_funct_2(sK4,sK0,sK3)),
% 1.78/0.64    inference(cnf_transformation,[],[f42])).
% 1.78/0.64  fof(f105,plain,(
% 1.78/0.64    ~spl5_1 | ~spl5_2 | ~spl5_3),
% 1.78/0.64    inference(avatar_split_clause,[],[f55,f102,f98,f94])).
% 1.78/0.64  fof(f55,plain,(
% 1.78/0.64    ~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))),
% 1.78/0.64    inference(cnf_transformation,[],[f42])).
% 1.78/0.64  % SZS output end Proof for theBenchmark
% 1.78/0.64  % (16238)------------------------------
% 1.78/0.64  % (16238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.64  % (16238)Termination reason: Refutation
% 1.78/0.64  
% 1.78/0.64  % (16238)Memory used [KB]: 10874
% 1.78/0.64  % (16238)Time elapsed: 0.177 s
% 1.78/0.64  % (16238)------------------------------
% 1.78/0.64  % (16238)------------------------------
% 1.78/0.64  % (16226)Success in time 0.268 s
%------------------------------------------------------------------------------
