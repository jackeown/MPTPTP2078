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
% DateTime   : Thu Dec  3 13:14:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  218 (3909 expanded)
%              Number of leaves         :   31 (1407 expanded)
%              Depth                    :   30
%              Number of atoms          :  884 (28887 expanded)
%              Number of equality atoms :  149 (4186 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f909,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f191,f196,f311,f339,f366,f429,f439,f501,f621,f841,f908])).

fof(f908,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_15
    | ~ spl3_21 ),
    inference(avatar_contradiction_clause,[],[f907])).

fof(f907,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_15
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f906,f86])).

fof(f86,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f34,f74,f73,f72])).

fof(f72,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
                & v2_funct_1(X2)
                & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2)
            & v2_funct_1(X2)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2)
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_struct_0(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,
    ( ? [X2] :
        ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2)
        & v2_funct_1(X2)
        & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
      & v2_funct_1(sK2)
      & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( ( l1_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                 => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f30])).

fof(f30,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).

fof(f906,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_15
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f900,f833])).

fof(f833,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f264,f828])).

fof(f828,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f827,f185])).

fof(f185,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f827,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f826,f86])).

fof(f826,plain,
    ( ~ v1_funct_1(sK2)
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f823,f264])).

fof(f823,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ v1_funct_1(sK2)
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f584,f263])).

fof(f263,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f163,f241])).

fof(f241,plain,(
    k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f182,f180])).

fof(f180,plain,(
    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(resolution,[],[f179,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f179,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f178,f148])).

fof(f148,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f83,f102])).

fof(f102,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f83,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f75])).

fof(f178,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f88,f151])).

fof(f151,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f85,f102])).

fof(f85,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f75])).

fof(f88,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f75])).

fof(f182,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(forward_demodulation,[],[f181,f148])).

fof(f181,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(forward_demodulation,[],[f89,f151])).

fof(f89,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f75])).

fof(f163,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f158,f151])).

fof(f158,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f87,f148])).

fof(f87,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f75])).

fof(f584,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X0,X1,k2_relat_1(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(sK2))))
      | ~ v1_funct_1(X0)
      | k1_relat_1(X0) = X1
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f583,f136])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f583,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(sK2))))
      | ~ v1_funct_2(X0,X1,k2_relat_1(sK2))
      | k1_relat_1(X0) = X1
      | ~ v4_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f268,f137])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f268,plain,(
    ! [X0,X1] :
      ( v1_partfun1(X0,X1)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(sK2))))
      | ~ v1_funct_2(X0,X1,k2_relat_1(sK2)) ) ),
    inference(resolution,[],[f262,f129])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X1)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f262,plain,(
    ~ v1_xboole_0(k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f161,f241])).

fof(f161,plain,(
    ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f150,f151])).

fof(f150,plain,(
    ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(global_subsumption,[],[f85,f149])).

fof(f149,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f84,f115])).

fof(f115,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f84,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f75])).

fof(f264,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    inference(backward_demodulation,[],[f179,f241])).

fof(f900,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_1(sK2)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_15
    | ~ spl3_21 ),
    inference(resolution,[],[f886,f832])).

fof(f832,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f263,f828])).

fof(f886,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
        | ~ v1_funct_1(X0) )
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_15
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f885,f86])).

fof(f885,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
        | ~ v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_1(sK2) )
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_15
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f884,f832])).

fof(f884,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
        | ~ v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
        | ~ v1_funct_1(sK2) )
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_15
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f883,f833])).

fof(f883,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
        | ~ v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
        | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
        | ~ v1_funct_1(sK2) )
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_15
    | ~ spl3_21 ),
    inference(resolution,[],[f882,f92])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

fof(f882,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_15
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f843,f616])).

fof(f616,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f614])).

fof(f614,plain,
    ( spl3_21
  <=> sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f843,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(k2_funct_1(sK2)),sK2)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f837,f571])).

fof(f571,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f487,f490])).

fof(f490,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f489])).

fof(f489,plain,
    ( spl3_15
  <=> v2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f487,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f486,f423])).

fof(f423,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f422])).

fof(f422,plain,
    ( spl3_11
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f486,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f485,f428])).

fof(f428,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f426])).

fof(f426,plain,
    ( spl3_12
  <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f485,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f470,f463])).

fof(f463,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f391,f423])).

fof(f391,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f390,f232])).

fof(f232,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f155,f185])).

fof(f155,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f153,f86])).

fof(f153,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f90,f98])).

fof(f98,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f90,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f75])).

fof(f390,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f381,f296])).

fof(f296,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f295])).

fof(f295,plain,
    ( spl3_5
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f381,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_4 ),
    inference(superposition,[],[f108,f190])).

fof(f190,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl3_4
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f108,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f470,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(trivial_inequality_removal,[],[f469])).

fof(f469,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(superposition,[],[f93,f465])).

fof(f465,plain,
    ( k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f464,f232])).

fof(f464,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(resolution,[],[f463,f105])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f837,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2)
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f292,f828])).

fof(f292,plain,(
    ~ r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),sK2) ),
    inference(backward_demodulation,[],[f267,f271])).

fof(f271,plain,(
    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(forward_demodulation,[],[f220,f241])).

fof(f220,plain,(
    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(subsumption_resolution,[],[f219,f86])).

fof(f219,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f218,f163])).

fof(f218,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f217,f179])).

fof(f217,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f201,f90])).

fof(f201,plain,
    ( ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(trivial_inequality_removal,[],[f200])).

fof(f200,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f93,f182])).

fof(f267,plain,(
    ~ r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2) ),
    inference(backward_demodulation,[],[f231,f241])).

fof(f231,plain,(
    ~ r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) ),
    inference(forward_demodulation,[],[f230,f148])).

fof(f230,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) ),
    inference(forward_demodulation,[],[f91,f151])).

fof(f91,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f75])).

fof(f841,plain,
    ( ~ spl3_3
    | spl3_22 ),
    inference(avatar_contradiction_clause,[],[f840])).

fof(f840,plain,
    ( $false
    | ~ spl3_3
    | spl3_22 ),
    inference(trivial_inequality_removal,[],[f839])).

fof(f839,plain,
    ( k6_partfun1(k1_relat_1(sK2)) != k6_partfun1(k1_relat_1(sK2))
    | ~ spl3_3
    | spl3_22 ),
    inference(backward_demodulation,[],[f620,f828])).

fof(f620,plain,
    ( k6_partfun1(k2_struct_0(sK0)) != k6_partfun1(k1_relat_1(sK2))
    | spl3_22 ),
    inference(avatar_component_clause,[],[f618])).

fof(f618,plain,
    ( spl3_22
  <=> k6_partfun1(k2_struct_0(sK0)) = k6_partfun1(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f621,plain,
    ( spl3_21
    | ~ spl3_22
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_11
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f612,f489,f422,f336,f295,f188,f184,f618,f614])).

fof(f336,plain,
    ( spl3_9
  <=> k6_partfun1(k2_struct_0(sK0)) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f612,plain,
    ( k6_partfun1(k2_struct_0(sK0)) != k6_partfun1(k1_relat_1(sK2))
    | sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_11
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f611,f423])).

fof(f611,plain,
    ( k6_partfun1(k2_struct_0(sK0)) != k6_partfun1(k1_relat_1(sK2))
    | sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f403,f490])).

fof(f403,plain,
    ( k6_partfun1(k2_struct_0(sK0)) != k6_partfun1(k1_relat_1(sK2))
    | sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f402,f232])).

fof(f402,plain,
    ( k6_partfun1(k2_struct_0(sK0)) != k6_partfun1(k2_relat_1(k2_funct_1(sK2)))
    | sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f401,f296])).

fof(f401,plain,
    ( k6_partfun1(k2_struct_0(sK0)) != k6_partfun1(k2_relat_1(k2_funct_1(sK2)))
    | sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f400,f185])).

fof(f400,plain,
    ( k6_partfun1(k2_struct_0(sK0)) != k6_partfun1(k2_relat_1(k2_funct_1(sK2)))
    | sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f399,f86])).

fof(f399,plain,
    ( k6_partfun1(k2_struct_0(sK0)) != k6_partfun1(k2_relat_1(k2_funct_1(sK2)))
    | sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f398,f190])).

fof(f398,plain,
    ( k6_partfun1(k2_struct_0(sK0)) != k6_partfun1(k2_relat_1(k2_funct_1(sK2)))
    | sK2 = k2_funct_1(k2_funct_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_9 ),
    inference(superposition,[],[f140,f338])).

fof(f338,plain,
    ( k6_partfun1(k2_struct_0(sK0)) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f336])).

fof(f140,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k2_funct_1(X0) = X1
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f118,f125])).

fof(f125,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f118,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

fof(f501,plain,
    ( ~ spl3_3
    | spl3_15 ),
    inference(avatar_contradiction_clause,[],[f500])).

fof(f500,plain,
    ( $false
    | ~ spl3_3
    | spl3_15 ),
    inference(subsumption_resolution,[],[f499,f185])).

fof(f499,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_15 ),
    inference(subsumption_resolution,[],[f498,f86])).

fof(f498,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_15 ),
    inference(subsumption_resolution,[],[f497,f90])).

fof(f497,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_15 ),
    inference(resolution,[],[f491,f101])).

fof(f101,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f491,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | spl3_15 ),
    inference(avatar_component_clause,[],[f489])).

fof(f439,plain,
    ( ~ spl3_3
    | spl3_11 ),
    inference(avatar_contradiction_clause,[],[f438])).

fof(f438,plain,
    ( $false
    | ~ spl3_3
    | spl3_11 ),
    inference(subsumption_resolution,[],[f437,f185])).

fof(f437,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_11 ),
    inference(subsumption_resolution,[],[f436,f86])).

fof(f436,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_11 ),
    inference(subsumption_resolution,[],[f431,f90])).

fof(f431,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_11 ),
    inference(resolution,[],[f424,f100])).

fof(f100,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f424,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f422])).

fof(f429,plain,
    ( ~ spl3_11
    | spl3_12
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f389,f295,f188,f184,f426,f422])).

fof(f389,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f388,f232])).

fof(f388,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f380,f296])).

fof(f380,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_4 ),
    inference(superposition,[],[f107,f190])).

fof(f107,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f366,plain,(
    ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f365])).

fof(f365,plain,
    ( $false
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f349,f127])).

fof(f127,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f349,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl3_8 ),
    inference(backward_demodulation,[],[f262,f328])).

fof(f328,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f326])).

fof(f326,plain,
    ( spl3_8
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f339,plain,
    ( spl3_9
    | spl3_8 ),
    inference(avatar_split_clause,[],[f319,f326,f336])).

fof(f319,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | k6_partfun1(k2_struct_0(sK0)) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f208,f241])).

fof(f208,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | k6_partfun1(k2_struct_0(sK0)) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f207,f86])).

fof(f207,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | k6_partfun1(k2_struct_0(sK0)) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f206,f163])).

fof(f206,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | k6_partfun1(k2_struct_0(sK0)) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f205,f179])).

fof(f205,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | k6_partfun1(k2_struct_0(sK0)) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f204,f90])).

fof(f204,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | k6_partfun1(k2_struct_0(sK0)) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(trivial_inequality_removal,[],[f197])).

fof(f197,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | k1_xboole_0 = k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | k6_partfun1(k2_struct_0(sK0)) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f103,f182])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(f311,plain,
    ( ~ spl3_3
    | spl3_5 ),
    inference(avatar_contradiction_clause,[],[f310])).

fof(f310,plain,
    ( $false
    | ~ spl3_3
    | spl3_5 ),
    inference(subsumption_resolution,[],[f309,f185])).

fof(f309,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_5 ),
    inference(subsumption_resolution,[],[f308,f86])).

fof(f308,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_5 ),
    inference(subsumption_resolution,[],[f303,f90])).

fof(f303,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_5 ),
    inference(resolution,[],[f297,f99])).

fof(f99,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f297,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f295])).

fof(f196,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f195])).

fof(f195,plain,
    ( $false
    | spl3_3 ),
    inference(subsumption_resolution,[],[f193,f113])).

fof(f113,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f193,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))
    | spl3_3 ),
    inference(resolution,[],[f192,f179])).

fof(f192,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl3_3 ),
    inference(resolution,[],[f186,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f186,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f184])).

fof(f191,plain,
    ( ~ spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f154,f188,f184])).

fof(f154,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f152,f86])).

fof(f152,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f90,f97])).

fof(f97,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:48:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (31004)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.50  % (31009)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (31013)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.50  % (31014)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.51  % (31024)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.51  % (31017)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.51  % (31003)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.51  % (31008)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (31015)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (31025)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.52  % (31022)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.52  % (31006)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.52  % (31019)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.52  % (31029)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (31026)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.53  % (31002)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.53  % (31027)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.53  % (31018)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.53  % (31016)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.53  % (31021)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.53  % (31007)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.53  % (31031)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.53  % (31003)Refutation not found, incomplete strategy% (31003)------------------------------
% 0.20/0.53  % (31003)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (31003)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (31003)Memory used [KB]: 1791
% 0.20/0.53  % (31003)Time elapsed: 0.129 s
% 0.20/0.53  % (31003)------------------------------
% 0.20/0.53  % (31003)------------------------------
% 0.20/0.53  % (31032)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.53  % (31011)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.54  % (31012)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.54  % (31019)Refutation not found, incomplete strategy% (31019)------------------------------
% 0.20/0.54  % (31019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (31028)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.54  % (31019)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (31019)Memory used [KB]: 10746
% 0.20/0.54  % (31019)Time elapsed: 0.145 s
% 0.20/0.54  % (31019)------------------------------
% 0.20/0.54  % (31019)------------------------------
% 0.20/0.54  % (31023)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.54  % (31010)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.55  % (31033)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.55  % (31020)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.55  % (31033)Refutation not found, incomplete strategy% (31033)------------------------------
% 0.20/0.55  % (31033)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (31033)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (31033)Memory used [KB]: 1791
% 0.20/0.55  % (31033)Time elapsed: 0.149 s
% 0.20/0.55  % (31033)------------------------------
% 0.20/0.55  % (31033)------------------------------
% 0.20/0.56  % (31027)Refutation found. Thanks to Tanya!
% 0.20/0.56  % SZS status Theorem for theBenchmark
% 0.20/0.56  % SZS output start Proof for theBenchmark
% 0.20/0.56  fof(f909,plain,(
% 0.20/0.56    $false),
% 0.20/0.56    inference(avatar_sat_refutation,[],[f191,f196,f311,f339,f366,f429,f439,f501,f621,f841,f908])).
% 0.20/0.56  fof(f908,plain,(
% 0.20/0.56    ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_11 | ~spl3_12 | ~spl3_15 | ~spl3_21),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f907])).
% 0.20/0.56  fof(f907,plain,(
% 0.20/0.56    $false | (~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_11 | ~spl3_12 | ~spl3_15 | ~spl3_21)),
% 0.20/0.56    inference(subsumption_resolution,[],[f906,f86])).
% 0.20/0.56  fof(f86,plain,(
% 0.20/0.56    v1_funct_1(sK2)),
% 0.20/0.56    inference(cnf_transformation,[],[f75])).
% 0.20/0.56  fof(f75,plain,(
% 0.20/0.56    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f34,f74,f73,f72])).
% 0.20/0.56  fof(f72,plain,(
% 0.20/0.56    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f73,plain,(
% 0.20/0.56    ? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f74,plain,(
% 0.20/0.56    ? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f34,plain,(
% 0.20/0.56    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.20/0.56    inference(flattening,[],[f33])).
% 0.20/0.56  fof(f33,plain,(
% 0.20/0.56    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f31])).
% 0.20/0.56  fof(f31,negated_conjecture,(
% 0.20/0.56    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.20/0.56    inference(negated_conjecture,[],[f30])).
% 0.20/0.56  fof(f30,conjecture,(
% 0.20/0.56    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).
% 0.20/0.56  fof(f906,plain,(
% 0.20/0.56    ~v1_funct_1(sK2) | (~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_11 | ~spl3_12 | ~spl3_15 | ~spl3_21)),
% 0.20/0.56    inference(subsumption_resolution,[],[f900,f833])).
% 0.20/0.56  fof(f833,plain,(
% 0.20/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~spl3_3),
% 0.20/0.56    inference(backward_demodulation,[],[f264,f828])).
% 0.20/0.56  fof(f828,plain,(
% 0.20/0.56    k2_struct_0(sK0) = k1_relat_1(sK2) | ~spl3_3),
% 0.20/0.56    inference(subsumption_resolution,[],[f827,f185])).
% 0.20/0.56  fof(f185,plain,(
% 0.20/0.56    v1_relat_1(sK2) | ~spl3_3),
% 0.20/0.56    inference(avatar_component_clause,[],[f184])).
% 0.20/0.56  fof(f184,plain,(
% 0.20/0.56    spl3_3 <=> v1_relat_1(sK2)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.56  fof(f827,plain,(
% 0.20/0.56    k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.56    inference(subsumption_resolution,[],[f826,f86])).
% 0.20/0.56  fof(f826,plain,(
% 0.20/0.56    ~v1_funct_1(sK2) | k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.56    inference(subsumption_resolution,[],[f823,f264])).
% 0.20/0.56  fof(f823,plain,(
% 0.20/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~v1_funct_1(sK2) | k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.56    inference(resolution,[],[f584,f263])).
% 0.20/0.56  fof(f263,plain,(
% 0.20/0.56    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 0.20/0.56    inference(backward_demodulation,[],[f163,f241])).
% 0.20/0.56  fof(f241,plain,(
% 0.20/0.56    k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.20/0.56    inference(backward_demodulation,[],[f182,f180])).
% 0.20/0.56  fof(f180,plain,(
% 0.20/0.56    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.20/0.56    inference(resolution,[],[f179,f105])).
% 0.20/0.56  fof(f105,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f48])).
% 0.20/0.56  fof(f48,plain,(
% 0.20/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.56    inference(ennf_transformation,[],[f18])).
% 0.20/0.56  fof(f18,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.56  fof(f179,plain,(
% 0.20/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.20/0.56    inference(forward_demodulation,[],[f178,f148])).
% 0.20/0.56  fof(f148,plain,(
% 0.20/0.56    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.20/0.56    inference(resolution,[],[f83,f102])).
% 0.20/0.56  fof(f102,plain,(
% 0.20/0.56    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f45])).
% 0.20/0.56  fof(f45,plain,(
% 0.20/0.56    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f26])).
% 0.20/0.56  fof(f26,axiom,(
% 0.20/0.56    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.56  fof(f83,plain,(
% 0.20/0.56    l1_struct_0(sK0)),
% 0.20/0.56    inference(cnf_transformation,[],[f75])).
% 0.20/0.56  fof(f178,plain,(
% 0.20/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))),
% 0.20/0.56    inference(forward_demodulation,[],[f88,f151])).
% 0.20/0.56  fof(f151,plain,(
% 0.20/0.56    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.20/0.56    inference(resolution,[],[f85,f102])).
% 0.20/0.56  fof(f85,plain,(
% 0.20/0.56    l1_struct_0(sK1)),
% 0.20/0.56    inference(cnf_transformation,[],[f75])).
% 0.20/0.56  fof(f88,plain,(
% 0.20/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.56    inference(cnf_transformation,[],[f75])).
% 0.20/0.56  fof(f182,plain,(
% 0.20/0.56    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.20/0.56    inference(forward_demodulation,[],[f181,f148])).
% 0.20/0.56  fof(f181,plain,(
% 0.20/0.56    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.20/0.56    inference(forward_demodulation,[],[f89,f151])).
% 0.20/0.56  fof(f89,plain,(
% 0.20/0.56    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.20/0.56    inference(cnf_transformation,[],[f75])).
% 0.20/0.56  fof(f163,plain,(
% 0.20/0.56    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.20/0.56    inference(forward_demodulation,[],[f158,f151])).
% 0.20/0.56  fof(f158,plain,(
% 0.20/0.56    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.56    inference(backward_demodulation,[],[f87,f148])).
% 0.20/0.56  fof(f87,plain,(
% 0.20/0.56    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.56    inference(cnf_transformation,[],[f75])).
% 0.20/0.56  fof(f584,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~v1_funct_2(X0,X1,k2_relat_1(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(sK2)))) | ~v1_funct_1(X0) | k1_relat_1(X0) = X1 | ~v1_relat_1(X0)) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f583,f136])).
% 0.20/0.56  fof(f136,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f68])).
% 0.20/0.56  fof(f68,plain,(
% 0.20/0.56    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.56    inference(ennf_transformation,[],[f32])).
% 0.20/0.56  fof(f32,plain,(
% 0.20/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.20/0.56    inference(pure_predicate_removal,[],[f17])).
% 0.20/0.56  fof(f17,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.56  fof(f583,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(sK2)))) | ~v1_funct_2(X0,X1,k2_relat_1(sK2)) | k1_relat_1(X0) = X1 | ~v4_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 0.20/0.56    inference(resolution,[],[f268,f137])).
% 0.20/0.56  fof(f137,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | k1_relat_1(X1) = X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f82])).
% 0.20/0.56  fof(f82,plain,(
% 0.20/0.56    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.56    inference(nnf_transformation,[],[f70])).
% 0.20/0.56  fof(f70,plain,(
% 0.20/0.56    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.56    inference(flattening,[],[f69])).
% 0.20/0.56  fof(f69,plain,(
% 0.20/0.56    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.56    inference(ennf_transformation,[],[f20])).
% 0.20/0.56  fof(f20,axiom,(
% 0.20/0.56    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 0.20/0.56  fof(f268,plain,(
% 0.20/0.56    ( ! [X0,X1] : (v1_partfun1(X0,X1) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(sK2)))) | ~v1_funct_2(X0,X1,k2_relat_1(sK2))) )),
% 0.20/0.56    inference(resolution,[],[f262,f129])).
% 0.20/0.56  fof(f129,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (v1_xboole_0(X1) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_partfun1(X2,X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f65])).
% 0.20/0.56  fof(f65,plain,(
% 0.20/0.56    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.56    inference(flattening,[],[f64])).
% 0.20/0.56  fof(f64,plain,(
% 0.20/0.56    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.56    inference(ennf_transformation,[],[f19])).
% 0.20/0.56  fof(f19,axiom,(
% 0.20/0.56    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.20/0.56  fof(f262,plain,(
% 0.20/0.56    ~v1_xboole_0(k2_relat_1(sK2))),
% 0.20/0.56    inference(backward_demodulation,[],[f161,f241])).
% 0.20/0.56  fof(f161,plain,(
% 0.20/0.56    ~v1_xboole_0(k2_struct_0(sK1))),
% 0.20/0.56    inference(backward_demodulation,[],[f150,f151])).
% 0.20/0.56  fof(f150,plain,(
% 0.20/0.56    ~v1_xboole_0(u1_struct_0(sK1))),
% 0.20/0.56    inference(global_subsumption,[],[f85,f149])).
% 0.20/0.56  fof(f149,plain,(
% 0.20/0.56    ~l1_struct_0(sK1) | ~v1_xboole_0(u1_struct_0(sK1))),
% 0.20/0.56    inference(resolution,[],[f84,f115])).
% 0.20/0.56  fof(f115,plain,(
% 0.20/0.56    ( ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f55])).
% 0.20/0.57  fof(f55,plain,(
% 0.20/0.57    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.57    inference(flattening,[],[f54])).
% 0.20/0.57  fof(f54,plain,(
% 0.20/0.57    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f28])).
% 0.20/0.57  fof(f28,axiom,(
% 0.20/0.57    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.57  fof(f84,plain,(
% 0.20/0.57    ~v2_struct_0(sK1)),
% 0.20/0.57    inference(cnf_transformation,[],[f75])).
% 0.20/0.57  fof(f264,plain,(
% 0.20/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 0.20/0.57    inference(backward_demodulation,[],[f179,f241])).
% 0.20/0.57  fof(f900,plain,(
% 0.20/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_1(sK2) | (~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_11 | ~spl3_12 | ~spl3_15 | ~spl3_21)),
% 0.20/0.57    inference(resolution,[],[f886,f832])).
% 0.20/0.57  fof(f832,plain,(
% 0.20/0.57    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~spl3_3),
% 0.20/0.57    inference(backward_demodulation,[],[f263,f828])).
% 0.20/0.57  fof(f886,plain,(
% 0.20/0.57    ( ! [X0] : (~v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_1(X0)) ) | (~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_11 | ~spl3_12 | ~spl3_15 | ~spl3_21)),
% 0.20/0.57    inference(subsumption_resolution,[],[f885,f86])).
% 0.20/0.57  fof(f885,plain,(
% 0.20/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(X0) | ~v1_funct_1(sK2)) ) | (~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_11 | ~spl3_12 | ~spl3_15 | ~spl3_21)),
% 0.20/0.57    inference(subsumption_resolution,[],[f884,f832])).
% 0.20/0.57  fof(f884,plain,(
% 0.20/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(X0) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2)) ) | (~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_11 | ~spl3_12 | ~spl3_15 | ~spl3_21)),
% 0.20/0.57    inference(subsumption_resolution,[],[f883,f833])).
% 0.20/0.57  fof(f883,plain,(
% 0.20/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2)) ) | (~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_11 | ~spl3_12 | ~spl3_15 | ~spl3_21)),
% 0.20/0.57    inference(resolution,[],[f882,f92])).
% 0.20/0.57  fof(f92,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f36])).
% 0.20/0.57  fof(f36,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.57    inference(flattening,[],[f35])).
% 0.20/0.57  fof(f35,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.57    inference(ennf_transformation,[],[f22])).
% 0.20/0.57  fof(f22,axiom,(
% 0.20/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).
% 0.20/0.57  fof(f882,plain,(
% 0.20/0.57    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | (~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_11 | ~spl3_12 | ~spl3_15 | ~spl3_21)),
% 0.20/0.57    inference(forward_demodulation,[],[f843,f616])).
% 0.20/0.57  fof(f616,plain,(
% 0.20/0.57    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~spl3_21),
% 0.20/0.57    inference(avatar_component_clause,[],[f614])).
% 0.20/0.57  fof(f614,plain,(
% 0.20/0.57    spl3_21 <=> sK2 = k2_funct_1(k2_funct_1(sK2))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.57  fof(f843,plain,(
% 0.20/0.57    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(k2_funct_1(sK2)),sK2) | (~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_11 | ~spl3_12 | ~spl3_15)),
% 0.20/0.57    inference(forward_demodulation,[],[f837,f571])).
% 0.20/0.57  fof(f571,plain,(
% 0.20/0.57    k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_11 | ~spl3_12 | ~spl3_15)),
% 0.20/0.57    inference(subsumption_resolution,[],[f487,f490])).
% 0.20/0.57  fof(f490,plain,(
% 0.20/0.57    v2_funct_1(k2_funct_1(sK2)) | ~spl3_15),
% 0.20/0.57    inference(avatar_component_clause,[],[f489])).
% 0.20/0.57  fof(f489,plain,(
% 0.20/0.57    spl3_15 <=> v2_funct_1(k2_funct_1(sK2))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.57  fof(f487,plain,(
% 0.20/0.57    ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_11 | ~spl3_12)),
% 0.20/0.57    inference(subsumption_resolution,[],[f486,f423])).
% 0.20/0.57  fof(f423,plain,(
% 0.20/0.57    v1_funct_1(k2_funct_1(sK2)) | ~spl3_11),
% 0.20/0.57    inference(avatar_component_clause,[],[f422])).
% 0.20/0.57  fof(f422,plain,(
% 0.20/0.57    spl3_11 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.57  fof(f486,plain,(
% 0.20/0.57    ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | (~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_11 | ~spl3_12)),
% 0.20/0.57    inference(subsumption_resolution,[],[f485,f428])).
% 0.20/0.57  fof(f428,plain,(
% 0.20/0.57    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~spl3_12),
% 0.20/0.57    inference(avatar_component_clause,[],[f426])).
% 0.20/0.57  fof(f426,plain,(
% 0.20/0.57    spl3_12 <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.57  fof(f485,plain,(
% 0.20/0.57    ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | (~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_11)),
% 0.20/0.57    inference(subsumption_resolution,[],[f470,f463])).
% 0.20/0.57  fof(f463,plain,(
% 0.20/0.57    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | (~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_11)),
% 0.20/0.57    inference(subsumption_resolution,[],[f391,f423])).
% 0.20/0.57  fof(f391,plain,(
% 0.20/0.57    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_funct_1(k2_funct_1(sK2)) | (~spl3_3 | ~spl3_4 | ~spl3_5)),
% 0.20/0.57    inference(forward_demodulation,[],[f390,f232])).
% 0.20/0.57  fof(f232,plain,(
% 0.20/0.57    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_3),
% 0.20/0.57    inference(subsumption_resolution,[],[f155,f185])).
% 0.20/0.57  fof(f155,plain,(
% 0.20/0.57    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.20/0.57    inference(subsumption_resolution,[],[f153,f86])).
% 0.20/0.57  fof(f153,plain,(
% 0.20/0.57    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.57    inference(resolution,[],[f90,f98])).
% 0.20/0.57  fof(f98,plain,(
% 0.20/0.57    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f42])).
% 0.20/0.57  fof(f42,plain,(
% 0.20/0.57    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.57    inference(flattening,[],[f41])).
% 0.20/0.57  fof(f41,plain,(
% 0.20/0.57    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f15])).
% 0.20/0.57  fof(f15,axiom,(
% 0.20/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.20/0.57  fof(f90,plain,(
% 0.20/0.57    v2_funct_1(sK2)),
% 0.20/0.57    inference(cnf_transformation,[],[f75])).
% 0.20/0.57  fof(f390,plain,(
% 0.20/0.57    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))) | ~v1_funct_1(k2_funct_1(sK2)) | (~spl3_4 | ~spl3_5)),
% 0.20/0.57    inference(subsumption_resolution,[],[f381,f296])).
% 0.20/0.57  fof(f296,plain,(
% 0.20/0.57    v1_relat_1(k2_funct_1(sK2)) | ~spl3_5),
% 0.20/0.57    inference(avatar_component_clause,[],[f295])).
% 0.20/0.57  fof(f295,plain,(
% 0.20/0.57    spl3_5 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.57  fof(f381,plain,(
% 0.20/0.57    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl3_4),
% 0.20/0.57    inference(superposition,[],[f108,f190])).
% 0.20/0.57  fof(f190,plain,(
% 0.20/0.57    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_4),
% 0.20/0.57    inference(avatar_component_clause,[],[f188])).
% 0.20/0.57  fof(f188,plain,(
% 0.20/0.57    spl3_4 <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.57  fof(f108,plain,(
% 0.20/0.57    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f50])).
% 0.20/0.57  fof(f50,plain,(
% 0.20/0.57    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.57    inference(flattening,[],[f49])).
% 0.20/0.57  fof(f49,plain,(
% 0.20/0.57    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f25])).
% 0.20/0.57  fof(f25,axiom,(
% 0.20/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 0.20/0.57  fof(f470,plain,(
% 0.20/0.57    ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | (~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_11)),
% 0.20/0.57    inference(trivial_inequality_removal,[],[f469])).
% 0.20/0.57  fof(f469,plain,(
% 0.20/0.57    k1_relat_1(sK2) != k1_relat_1(sK2) | ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | (~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_11)),
% 0.20/0.57    inference(superposition,[],[f93,f465])).
% 0.20/0.57  fof(f465,plain,(
% 0.20/0.57    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_11)),
% 0.20/0.57    inference(forward_demodulation,[],[f464,f232])).
% 0.20/0.57  fof(f464,plain,(
% 0.20/0.57    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_11)),
% 0.20/0.57    inference(resolution,[],[f463,f105])).
% 0.20/0.57  fof(f93,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f38])).
% 0.20/0.57  fof(f38,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.57    inference(flattening,[],[f37])).
% 0.20/0.57  fof(f37,plain,(
% 0.20/0.57    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.57    inference(ennf_transformation,[],[f29])).
% 0.20/0.57  fof(f29,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 0.20/0.57  fof(f837,plain,(
% 0.20/0.57    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2) | ~spl3_3),
% 0.20/0.57    inference(backward_demodulation,[],[f292,f828])).
% 0.20/0.57  fof(f292,plain,(
% 0.20/0.57    ~r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),sK2)),
% 0.20/0.57    inference(backward_demodulation,[],[f267,f271])).
% 0.20/0.57  fof(f271,plain,(
% 0.20/0.57    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.20/0.57    inference(forward_demodulation,[],[f220,f241])).
% 0.20/0.57  fof(f220,plain,(
% 0.20/0.57    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.20/0.57    inference(subsumption_resolution,[],[f219,f86])).
% 0.20/0.57  fof(f219,plain,(
% 0.20/0.57    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v1_funct_1(sK2)),
% 0.20/0.57    inference(subsumption_resolution,[],[f218,f163])).
% 0.20/0.57  fof(f218,plain,(
% 0.20/0.57    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 0.20/0.57    inference(subsumption_resolution,[],[f217,f179])).
% 0.20/0.57  fof(f217,plain,(
% 0.20/0.57    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 0.20/0.57    inference(subsumption_resolution,[],[f201,f90])).
% 0.20/0.57  fof(f201,plain,(
% 0.20/0.57    ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 0.20/0.57    inference(trivial_inequality_removal,[],[f200])).
% 0.20/0.57  fof(f200,plain,(
% 0.20/0.57    k2_struct_0(sK1) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 0.20/0.57    inference(superposition,[],[f93,f182])).
% 0.20/0.57  fof(f267,plain,(
% 0.20/0.57    ~r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2)),
% 0.20/0.57    inference(backward_demodulation,[],[f231,f241])).
% 0.20/0.57  fof(f231,plain,(
% 0.20/0.57    ~r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)),
% 0.20/0.57    inference(forward_demodulation,[],[f230,f148])).
% 0.20/0.57  fof(f230,plain,(
% 0.20/0.57    ~r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)),
% 0.20/0.57    inference(forward_demodulation,[],[f91,f151])).
% 0.20/0.57  fof(f91,plain,(
% 0.20/0.57    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 0.20/0.57    inference(cnf_transformation,[],[f75])).
% 0.20/0.57  fof(f841,plain,(
% 0.20/0.57    ~spl3_3 | spl3_22),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f840])).
% 0.20/0.57  fof(f840,plain,(
% 0.20/0.57    $false | (~spl3_3 | spl3_22)),
% 0.20/0.57    inference(trivial_inequality_removal,[],[f839])).
% 0.20/0.57  fof(f839,plain,(
% 0.20/0.57    k6_partfun1(k1_relat_1(sK2)) != k6_partfun1(k1_relat_1(sK2)) | (~spl3_3 | spl3_22)),
% 0.20/0.57    inference(backward_demodulation,[],[f620,f828])).
% 0.20/0.57  fof(f620,plain,(
% 0.20/0.57    k6_partfun1(k2_struct_0(sK0)) != k6_partfun1(k1_relat_1(sK2)) | spl3_22),
% 0.20/0.57    inference(avatar_component_clause,[],[f618])).
% 0.20/0.57  fof(f618,plain,(
% 0.20/0.57    spl3_22 <=> k6_partfun1(k2_struct_0(sK0)) = k6_partfun1(k1_relat_1(sK2))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.20/0.57  fof(f621,plain,(
% 0.20/0.57    spl3_21 | ~spl3_22 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_9 | ~spl3_11 | ~spl3_15),
% 0.20/0.57    inference(avatar_split_clause,[],[f612,f489,f422,f336,f295,f188,f184,f618,f614])).
% 0.20/0.57  fof(f336,plain,(
% 0.20/0.57    spl3_9 <=> k6_partfun1(k2_struct_0(sK0)) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.57  fof(f612,plain,(
% 0.20/0.57    k6_partfun1(k2_struct_0(sK0)) != k6_partfun1(k1_relat_1(sK2)) | sK2 = k2_funct_1(k2_funct_1(sK2)) | (~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_9 | ~spl3_11 | ~spl3_15)),
% 0.20/0.57    inference(subsumption_resolution,[],[f611,f423])).
% 0.20/0.57  fof(f611,plain,(
% 0.20/0.57    k6_partfun1(k2_struct_0(sK0)) != k6_partfun1(k1_relat_1(sK2)) | sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | (~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_9 | ~spl3_15)),
% 0.20/0.57    inference(subsumption_resolution,[],[f403,f490])).
% 0.20/0.57  fof(f403,plain,(
% 0.20/0.57    k6_partfun1(k2_struct_0(sK0)) != k6_partfun1(k1_relat_1(sK2)) | sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | (~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_9)),
% 0.20/0.57    inference(forward_demodulation,[],[f402,f232])).
% 0.20/0.57  fof(f402,plain,(
% 0.20/0.57    k6_partfun1(k2_struct_0(sK0)) != k6_partfun1(k2_relat_1(k2_funct_1(sK2))) | sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | (~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_9)),
% 0.20/0.57    inference(subsumption_resolution,[],[f401,f296])).
% 0.20/0.57  fof(f401,plain,(
% 0.20/0.57    k6_partfun1(k2_struct_0(sK0)) != k6_partfun1(k2_relat_1(k2_funct_1(sK2))) | sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_3 | ~spl3_4 | ~spl3_9)),
% 0.20/0.57    inference(subsumption_resolution,[],[f400,f185])).
% 0.20/0.57  fof(f400,plain,(
% 0.20/0.57    k6_partfun1(k2_struct_0(sK0)) != k6_partfun1(k2_relat_1(k2_funct_1(sK2))) | sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_4 | ~spl3_9)),
% 0.20/0.57    inference(subsumption_resolution,[],[f399,f86])).
% 0.20/0.57  fof(f399,plain,(
% 0.20/0.57    k6_partfun1(k2_struct_0(sK0)) != k6_partfun1(k2_relat_1(k2_funct_1(sK2))) | sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_4 | ~spl3_9)),
% 0.20/0.57    inference(subsumption_resolution,[],[f398,f190])).
% 0.20/0.57  fof(f398,plain,(
% 0.20/0.57    k6_partfun1(k2_struct_0(sK0)) != k6_partfun1(k2_relat_1(k2_funct_1(sK2))) | sK2 = k2_funct_1(k2_funct_1(sK2)) | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl3_9),
% 0.20/0.57    inference(superposition,[],[f140,f338])).
% 0.20/0.57  fof(f338,plain,(
% 0.20/0.57    k6_partfun1(k2_struct_0(sK0)) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~spl3_9),
% 0.20/0.57    inference(avatar_component_clause,[],[f336])).
% 0.20/0.57  fof(f140,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k2_funct_1(X0) = X1 | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.57    inference(definition_unfolding,[],[f118,f125])).
% 0.20/0.57  fof(f125,plain,(
% 0.20/0.57    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f21])).
% 0.20/0.57  fof(f21,axiom,(
% 0.20/0.57    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.20/0.57  fof(f118,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f59])).
% 0.20/0.57  fof(f59,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.57    inference(flattening,[],[f58])).
% 0.20/0.57  fof(f58,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f16])).
% 0.20/0.57  fof(f16,axiom,(
% 0.20/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).
% 0.20/0.57  fof(f501,plain,(
% 0.20/0.57    ~spl3_3 | spl3_15),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f500])).
% 0.20/0.57  fof(f500,plain,(
% 0.20/0.57    $false | (~spl3_3 | spl3_15)),
% 0.20/0.57    inference(subsumption_resolution,[],[f499,f185])).
% 0.20/0.57  fof(f499,plain,(
% 0.20/0.57    ~v1_relat_1(sK2) | spl3_15),
% 0.20/0.57    inference(subsumption_resolution,[],[f498,f86])).
% 0.20/0.57  fof(f498,plain,(
% 0.20/0.57    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_15),
% 0.20/0.57    inference(subsumption_resolution,[],[f497,f90])).
% 0.20/0.57  fof(f497,plain,(
% 0.20/0.57    ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_15),
% 0.20/0.57    inference(resolution,[],[f491,f101])).
% 0.20/0.57  fof(f101,plain,(
% 0.20/0.57    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f44])).
% 0.20/0.57  fof(f44,plain,(
% 0.20/0.57    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.57    inference(flattening,[],[f43])).
% 0.20/0.57  fof(f43,plain,(
% 0.20/0.57    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f12])).
% 0.20/0.57  fof(f12,axiom,(
% 0.20/0.57    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).
% 0.20/0.57  fof(f491,plain,(
% 0.20/0.57    ~v2_funct_1(k2_funct_1(sK2)) | spl3_15),
% 0.20/0.57    inference(avatar_component_clause,[],[f489])).
% 0.20/0.57  fof(f439,plain,(
% 0.20/0.57    ~spl3_3 | spl3_11),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f438])).
% 0.20/0.57  fof(f438,plain,(
% 0.20/0.57    $false | (~spl3_3 | spl3_11)),
% 0.20/0.57    inference(subsumption_resolution,[],[f437,f185])).
% 0.20/0.57  fof(f437,plain,(
% 0.20/0.57    ~v1_relat_1(sK2) | spl3_11),
% 0.20/0.57    inference(subsumption_resolution,[],[f436,f86])).
% 0.20/0.57  fof(f436,plain,(
% 0.20/0.57    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_11),
% 0.20/0.57    inference(subsumption_resolution,[],[f431,f90])).
% 0.20/0.57  fof(f431,plain,(
% 0.20/0.57    ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_11),
% 0.20/0.57    inference(resolution,[],[f424,f100])).
% 0.20/0.57  fof(f100,plain,(
% 0.20/0.57    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f44])).
% 0.20/0.57  fof(f424,plain,(
% 0.20/0.57    ~v1_funct_1(k2_funct_1(sK2)) | spl3_11),
% 0.20/0.57    inference(avatar_component_clause,[],[f422])).
% 0.20/0.57  fof(f429,plain,(
% 0.20/0.57    ~spl3_11 | spl3_12 | ~spl3_3 | ~spl3_4 | ~spl3_5),
% 0.20/0.57    inference(avatar_split_clause,[],[f389,f295,f188,f184,f426,f422])).
% 0.20/0.57  fof(f389,plain,(
% 0.20/0.57    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | (~spl3_3 | ~spl3_4 | ~spl3_5)),
% 0.20/0.57    inference(forward_demodulation,[],[f388,f232])).
% 0.20/0.57  fof(f388,plain,(
% 0.20/0.57    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) | ~v1_funct_1(k2_funct_1(sK2)) | (~spl3_4 | ~spl3_5)),
% 0.20/0.57    inference(subsumption_resolution,[],[f380,f296])).
% 0.20/0.57  fof(f380,plain,(
% 0.20/0.57    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl3_4),
% 0.20/0.57    inference(superposition,[],[f107,f190])).
% 0.20/0.57  fof(f107,plain,(
% 0.20/0.57    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f50])).
% 0.20/0.57  fof(f366,plain,(
% 0.20/0.57    ~spl3_8),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f365])).
% 0.20/0.57  fof(f365,plain,(
% 0.20/0.57    $false | ~spl3_8),
% 0.20/0.57    inference(subsumption_resolution,[],[f349,f127])).
% 0.20/0.57  fof(f127,plain,(
% 0.20/0.57    v1_xboole_0(k1_xboole_0)),
% 0.20/0.57    inference(cnf_transformation,[],[f1])).
% 0.20/0.57  fof(f1,axiom,(
% 0.20/0.57    v1_xboole_0(k1_xboole_0)),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.57  fof(f349,plain,(
% 0.20/0.57    ~v1_xboole_0(k1_xboole_0) | ~spl3_8),
% 0.20/0.57    inference(backward_demodulation,[],[f262,f328])).
% 0.20/0.57  fof(f328,plain,(
% 0.20/0.57    k1_xboole_0 = k2_relat_1(sK2) | ~spl3_8),
% 0.20/0.57    inference(avatar_component_clause,[],[f326])).
% 0.20/0.57  fof(f326,plain,(
% 0.20/0.57    spl3_8 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.57  fof(f339,plain,(
% 0.20/0.57    spl3_9 | spl3_8),
% 0.20/0.57    inference(avatar_split_clause,[],[f319,f326,f336])).
% 0.20/0.57  fof(f319,plain,(
% 0.20/0.57    k1_xboole_0 = k2_relat_1(sK2) | k6_partfun1(k2_struct_0(sK0)) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 0.20/0.57    inference(forward_demodulation,[],[f208,f241])).
% 0.20/0.57  fof(f208,plain,(
% 0.20/0.57    k1_xboole_0 = k2_struct_0(sK1) | k6_partfun1(k2_struct_0(sK0)) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 0.20/0.57    inference(subsumption_resolution,[],[f207,f86])).
% 0.20/0.57  fof(f207,plain,(
% 0.20/0.57    k1_xboole_0 = k2_struct_0(sK1) | k6_partfun1(k2_struct_0(sK0)) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2)),
% 0.20/0.57    inference(subsumption_resolution,[],[f206,f163])).
% 0.20/0.57  fof(f206,plain,(
% 0.20/0.57    k1_xboole_0 = k2_struct_0(sK1) | k6_partfun1(k2_struct_0(sK0)) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 0.20/0.57    inference(subsumption_resolution,[],[f205,f179])).
% 0.20/0.57  fof(f205,plain,(
% 0.20/0.57    k1_xboole_0 = k2_struct_0(sK1) | k6_partfun1(k2_struct_0(sK0)) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 0.20/0.57    inference(subsumption_resolution,[],[f204,f90])).
% 0.20/0.57  fof(f204,plain,(
% 0.20/0.57    k1_xboole_0 = k2_struct_0(sK1) | ~v2_funct_1(sK2) | k6_partfun1(k2_struct_0(sK0)) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 0.20/0.57    inference(trivial_inequality_removal,[],[f197])).
% 0.20/0.57  fof(f197,plain,(
% 0.20/0.57    k2_struct_0(sK1) != k2_struct_0(sK1) | k1_xboole_0 = k2_struct_0(sK1) | ~v2_funct_1(sK2) | k6_partfun1(k2_struct_0(sK0)) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 0.20/0.57    inference(superposition,[],[f103,f182])).
% 0.20/0.57  fof(f103,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f47])).
% 0.20/0.57  fof(f47,plain,(
% 0.20/0.57    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.57    inference(flattening,[],[f46])).
% 0.20/0.57  fof(f46,plain,(
% 0.20/0.57    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.57    inference(ennf_transformation,[],[f24])).
% 0.20/0.57  fof(f24,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 0.20/0.57  fof(f311,plain,(
% 0.20/0.57    ~spl3_3 | spl3_5),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f310])).
% 0.20/0.57  fof(f310,plain,(
% 0.20/0.57    $false | (~spl3_3 | spl3_5)),
% 0.20/0.57    inference(subsumption_resolution,[],[f309,f185])).
% 0.20/0.57  fof(f309,plain,(
% 0.20/0.57    ~v1_relat_1(sK2) | spl3_5),
% 0.20/0.57    inference(subsumption_resolution,[],[f308,f86])).
% 0.20/0.57  fof(f308,plain,(
% 0.20/0.57    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_5),
% 0.20/0.57    inference(subsumption_resolution,[],[f303,f90])).
% 0.20/0.57  fof(f303,plain,(
% 0.20/0.57    ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_5),
% 0.20/0.57    inference(resolution,[],[f297,f99])).
% 0.20/0.57  fof(f99,plain,(
% 0.20/0.57    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f44])).
% 0.20/0.57  fof(f297,plain,(
% 0.20/0.57    ~v1_relat_1(k2_funct_1(sK2)) | spl3_5),
% 0.20/0.57    inference(avatar_component_clause,[],[f295])).
% 0.20/0.57  fof(f196,plain,(
% 0.20/0.57    spl3_3),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f195])).
% 0.20/0.57  fof(f195,plain,(
% 0.20/0.57    $false | spl3_3),
% 0.20/0.57    inference(subsumption_resolution,[],[f193,f113])).
% 0.20/0.57  fof(f113,plain,(
% 0.20/0.57    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f7])).
% 0.20/0.57  fof(f7,axiom,(
% 0.20/0.57    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.57  fof(f193,plain,(
% 0.20/0.57    ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) | spl3_3),
% 0.20/0.57    inference(resolution,[],[f192,f179])).
% 0.20/0.57  fof(f192,plain,(
% 0.20/0.57    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl3_3),
% 0.20/0.57    inference(resolution,[],[f186,f109])).
% 0.20/0.57  fof(f109,plain,(
% 0.20/0.57    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f51])).
% 0.20/0.57  fof(f51,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.57    inference(ennf_transformation,[],[f5])).
% 0.20/0.57  fof(f5,axiom,(
% 0.20/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.57  fof(f186,plain,(
% 0.20/0.57    ~v1_relat_1(sK2) | spl3_3),
% 0.20/0.57    inference(avatar_component_clause,[],[f184])).
% 0.20/0.57  fof(f191,plain,(
% 0.20/0.57    ~spl3_3 | spl3_4),
% 0.20/0.57    inference(avatar_split_clause,[],[f154,f188,f184])).
% 0.20/0.57  fof(f154,plain,(
% 0.20/0.57    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.20/0.57    inference(subsumption_resolution,[],[f152,f86])).
% 0.20/0.57  fof(f152,plain,(
% 0.20/0.57    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.57    inference(resolution,[],[f90,f97])).
% 0.20/0.57  fof(f97,plain,(
% 0.20/0.57    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f42])).
% 0.20/0.57  % SZS output end Proof for theBenchmark
% 0.20/0.57  % (31027)------------------------------
% 0.20/0.57  % (31027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (31027)Termination reason: Refutation
% 0.20/0.57  
% 0.20/0.57  % (31027)Memory used [KB]: 11129
% 0.20/0.57  % (31027)Time elapsed: 0.153 s
% 0.20/0.57  % (31027)------------------------------
% 0.20/0.57  % (31027)------------------------------
% 0.20/0.57  % (30999)Success in time 0.216 s
%------------------------------------------------------------------------------
