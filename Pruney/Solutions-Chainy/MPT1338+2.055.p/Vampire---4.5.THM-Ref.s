%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  144 (2398 expanded)
%              Number of leaves         :   22 ( 867 expanded)
%              Depth                    :   22
%              Number of atoms          :  456 (19675 expanded)
%              Number of equality atoms :  159 (6551 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f348,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f148,f228,f236,f262,f345])).

fof(f345,plain,
    ( spl4_4
    | ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f344])).

fof(f344,plain,
    ( $false
    | spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f343,f101])).

fof(f101,plain,(
    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f100,f98])).

fof(f98,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f60,f81])).

fof(f81,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) ),
    inference(backward_demodulation,[],[f75,f73])).

fof(f73,plain,(
    u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(resolution,[],[f54,f43])).

fof(f43,plain,(
    l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))
      | k2_struct_0(sK2) != k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) )
    & v2_funct_1(sK3)
    & k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    & v1_funct_1(sK3)
    & l1_struct_0(sK2)
    & ~ v2_struct_0(sK2)
    & l1_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f17,f38,f37,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                  | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
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
              ( ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X2))
              | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X2)) )
            & v2_funct_1(X2)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),X2))
            | k2_struct_0(sK2) != k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),X2)) )
          & v2_funct_1(X2)
          & k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
          & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK2))
          & v1_funct_1(X2) )
      & l1_struct_0(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X2] :
        ( ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),X2))
          | k2_struct_0(sK2) != k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),X2)) )
        & v2_funct_1(X2)
        & k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
        & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK2))
        & v1_funct_1(X2) )
   => ( ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))
        | k2_struct_0(sK2) != k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) )
      & v2_funct_1(sK3)
      & k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
      & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
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
                 => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                    & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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
               => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                  & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).

fof(f54,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f75,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(backward_demodulation,[],[f46,f72])).

fof(f72,plain,(
    k2_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(resolution,[],[f54,f41])).

fof(f41,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f46,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f100,plain,
    ( k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f99,f44])).

fof(f44,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f99,plain,
    ( k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f56,f48])).

fof(f48,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f343,plain,
    ( k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f342,f293])).

fof(f293,plain,
    ( k2_funct_1(sK3) = k2_tops_2(k1_relat_1(sK3),k2_relat_1(sK3),sK3)
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f161,f232])).

fof(f232,plain,
    ( k2_struct_0(sK1) = k1_relat_1(sK3)
    | ~ spl4_5 ),
    inference(superposition,[],[f70,f229])).

fof(f229,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k6_partfun1(k2_struct_0(sK1)))
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f128,f223])).

fof(f223,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k2_struct_0(sK1))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl4_5
  <=> k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f128,plain,(
    k1_relat_1(sK3) = k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) ),
    inference(subsumption_resolution,[],[f127,f98])).

fof(f127,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3)))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f126,f44])).

fof(f126,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3)))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f59,f48])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

fof(f70,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f53,f51])).

fof(f51,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f53,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f161,plain,(
    k2_funct_1(sK3) = k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3) ),
    inference(subsumption_resolution,[],[f160,f44])).

fof(f160,plain,
    ( k2_funct_1(sK3) = k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f159,f110])).

fof(f110,plain,(
    v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) ),
    inference(backward_demodulation,[],[f82,f107])).

fof(f107,plain,(
    k2_struct_0(sK2) = k2_relat_1(sK3) ),
    inference(backward_demodulation,[],[f80,f106])).

fof(f106,plain,(
    k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f62,f81])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f80,plain,(
    k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) ),
    inference(backward_demodulation,[],[f76,f73])).

fof(f76,plain,(
    k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK2),sK3) ),
    inference(backward_demodulation,[],[f47,f72])).

fof(f47,plain,(
    k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f82,plain,(
    v1_funct_2(sK3,k2_struct_0(sK1),k2_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f74,f73])).

fof(f74,plain,(
    v1_funct_2(sK3,k2_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f45,f72])).

fof(f45,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f39])).

fof(f159,plain,
    ( k2_funct_1(sK3) = k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)
    | ~ v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f158,f109])).

fof(f109,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) ),
    inference(backward_demodulation,[],[f81,f107])).

fof(f158,plain,
    ( k2_funct_1(sK3) = k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3))))
    | ~ v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f157,f48])).

fof(f157,plain,
    ( ~ v2_funct_1(sK3)
    | k2_funct_1(sK3) = k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3))))
    | ~ v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(trivial_inequality_removal,[],[f154])).

fof(f154,plain,
    ( k2_relat_1(sK3) != k2_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | k2_funct_1(sK3) = k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3))))
    | ~ v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(superposition,[],[f67,f114])).

fof(f114,plain,(
    k2_relat_1(sK3) = k2_relset_1(k2_struct_0(sK1),k2_relat_1(sK3),sK3) ),
    inference(backward_demodulation,[],[f106,f107])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f342,plain,
    ( k2_relat_1(sK3) != k1_relat_1(k2_tops_2(k1_relat_1(sK3),k2_relat_1(sK3),sK3))
    | spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f147,f232])).

fof(f147,plain,
    ( k2_relat_1(sK3) != k1_relat_1(k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl4_4
  <=> k2_relat_1(sK3) = k1_relat_1(k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f262,plain,(
    ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f261])).

fof(f261,plain,
    ( $false
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f242,f50])).

fof(f50,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f242,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f112,f227])).

fof(f227,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f225])).

fof(f225,plain,
    ( spl4_6
  <=> k1_xboole_0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f112,plain,(
    ~ v1_xboole_0(k2_relat_1(sK3)) ),
    inference(backward_demodulation,[],[f88,f107])).

fof(f88,plain,(
    ~ v1_xboole_0(k2_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f87,f42])).

fof(f42,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f87,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK2))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f85,f43])).

fof(f85,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK2))
    | ~ l1_struct_0(sK2)
    | v2_struct_0(sK2) ),
    inference(superposition,[],[f55,f73])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f236,plain,
    ( spl4_3
    | ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f235])).

fof(f235,plain,
    ( $false
    | spl4_3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f232,f168])).

fof(f168,plain,
    ( k2_struct_0(sK1) != k1_relat_1(sK3)
    | spl4_3 ),
    inference(forward_demodulation,[],[f164,f104])).

fof(f104,plain,(
    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f103,f98])).

fof(f103,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f102,f44])).

fof(f102,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f57,f48])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f164,plain,
    ( k2_struct_0(sK1) != k2_relat_1(k2_funct_1(sK3))
    | spl4_3 ),
    inference(backward_demodulation,[],[f149,f161])).

fof(f149,plain,
    ( k2_struct_0(sK1) != k2_relat_1(k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3))
    | spl4_3 ),
    inference(superposition,[],[f143,f135])).

fof(f135,plain,(
    k2_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)) = k2_relat_1(k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)) ),
    inference(resolution,[],[f120,f132])).

fof(f132,plain,(
    sP0(k2_struct_0(sK1),k2_relat_1(sK3),sK3) ),
    inference(subsumption_resolution,[],[f131,f44])).

fof(f131,plain,
    ( sP0(k2_struct_0(sK1),k2_relat_1(sK3),sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f129,f110])).

fof(f129,plain,
    ( sP0(k2_struct_0(sK1),k2_relat_1(sK3),sK3)
    | ~ v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f66,f109])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X1,X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( sP0(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f29,f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ sP0(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | k2_relset_1(X1,X0,k2_tops_2(X0,X1,X2)) = k2_relat_1(k2_tops_2(X0,X1,X2)) ) ),
    inference(resolution,[],[f65,f62])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f40])).

% (21320)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f143,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl4_3
  <=> k2_struct_0(sK1) = k2_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f228,plain,
    ( spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f219,f225,f221])).

% (21319)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
fof(f219,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k2_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f218,f44])).

fof(f218,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k2_struct_0(sK1))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f217,f110])).

fof(f217,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k2_struct_0(sK1))
    | ~ v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f216,f109])).

fof(f216,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k2_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3))))
    | ~ v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f215,f48])).

fof(f215,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k2_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3))))
    | ~ v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(trivial_inequality_removal,[],[f211])).

fof(f211,plain,
    ( k2_relat_1(sK3) != k2_relat_1(sK3)
    | k1_xboole_0 = k2_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k2_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3))))
    | ~ v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(superposition,[],[f68,f114])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f148,plain,
    ( ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f139,f145,f141])).

% (21326)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
fof(f139,plain,
    ( k2_relat_1(sK3) != k1_relat_1(k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3))
    | k2_struct_0(sK1) != k2_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)) ),
    inference(backward_demodulation,[],[f115,f137])).

fof(f137,plain,(
    k1_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)) = k1_relat_1(k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)) ),
    inference(resolution,[],[f121,f132])).

% (21325)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
fof(f121,plain,(
    ! [X4,X5,X3] :
      ( ~ sP0(X3,X4,X5)
      | k1_relset_1(X4,X3,k2_tops_2(X3,X4,X5)) = k1_relat_1(k2_tops_2(X3,X4,X5)) ) ),
    inference(resolution,[],[f65,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f115,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3))
    | k2_relat_1(sK3) != k1_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)) ),
    inference(forward_demodulation,[],[f111,f107])).

fof(f111,plain,
    ( k2_relat_1(sK3) != k1_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) ),
    inference(backward_demodulation,[],[f83,f107])).

fof(f83,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3))
    | k2_struct_0(sK2) != k1_relset_1(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) ),
    inference(forward_demodulation,[],[f79,f73])).

fof(f79,plain,
    ( k2_struct_0(sK2) != k1_relset_1(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3))
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK2),sK3)) ),
    inference(backward_demodulation,[],[f78,f73])).

fof(f78,plain,
    ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK2),sK3))
    | k2_struct_0(sK2) != k1_relset_1(u1_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK2),sK3)) ),
    inference(forward_demodulation,[],[f77,f72])).

fof(f77,plain,
    ( k2_struct_0(sK2) != k1_relset_1(u1_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK2),sK3))
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) ),
    inference(backward_demodulation,[],[f49,f72])).

fof(f49,plain,
    ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))
    | k2_struct_0(sK2) != k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:05:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.44  % (21323)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.46  % (21323)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f348,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f148,f228,f236,f262,f345])).
% 0.21/0.46  fof(f345,plain,(
% 0.21/0.46    spl4_4 | ~spl4_5),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f344])).
% 0.21/0.46  fof(f344,plain,(
% 0.21/0.46    $false | (spl4_4 | ~spl4_5)),
% 0.21/0.46    inference(subsumption_resolution,[],[f343,f101])).
% 0.21/0.46  fof(f101,plain,(
% 0.21/0.46    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))),
% 0.21/0.46    inference(subsumption_resolution,[],[f100,f98])).
% 0.21/0.46  fof(f98,plain,(
% 0.21/0.46    v1_relat_1(sK3)),
% 0.21/0.46    inference(resolution,[],[f60,f81])).
% 0.21/0.46  fof(f81,plain,(
% 0.21/0.46    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))))),
% 0.21/0.46    inference(backward_demodulation,[],[f75,f73])).
% 0.21/0.46  fof(f73,plain,(
% 0.21/0.46    u1_struct_0(sK2) = k2_struct_0(sK2)),
% 0.21/0.46    inference(resolution,[],[f54,f43])).
% 0.21/0.46  fof(f43,plain,(
% 0.21/0.46    l1_struct_0(sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f39])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    (((k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) | k2_struct_0(sK2) != k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))) & v2_funct_1(sK3) & k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK3)) & l1_struct_0(sK2) & ~v2_struct_0(sK2)) & l1_struct_0(sK1)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f17,f38,f37,f36])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK1))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    ? [X1] : (? [X2] : ((k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),X2)) | k2_struct_0(sK2) != k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),X2))) & v2_funct_1(X2) & k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(X2)) & l1_struct_0(sK2) & ~v2_struct_0(sK2))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    ? [X2] : ((k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),X2)) | k2_struct_0(sK2) != k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),X2))) & v2_funct_1(X2) & k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(X2)) => ((k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) | k2_struct_0(sK2) != k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))) & v2_funct_1(sK3) & k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK3))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (? [X2] : (((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,negated_conjecture,(
% 0.21/0.46    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.21/0.46    inference(negated_conjecture,[],[f14])).
% 0.21/0.46  fof(f14,conjecture,(
% 0.21/0.46    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).
% 0.21/0.46  fof(f54,plain,(
% 0.21/0.46    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,axiom,(
% 0.21/0.46    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.46  fof(f75,plain,(
% 0.21/0.46    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK2))))),
% 0.21/0.46    inference(backward_demodulation,[],[f46,f72])).
% 0.21/0.46  fof(f72,plain,(
% 0.21/0.46    k2_struct_0(sK1) = u1_struct_0(sK1)),
% 0.21/0.46    inference(resolution,[],[f54,f41])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    l1_struct_0(sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f39])).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))),
% 0.21/0.46    inference(cnf_transformation,[],[f39])).
% 0.21/0.46  fof(f60,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.46  fof(f100,plain,(
% 0.21/0.46    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3)),
% 0.21/0.46    inference(subsumption_resolution,[],[f99,f44])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    v1_funct_1(sK3)),
% 0.21/0.46    inference(cnf_transformation,[],[f39])).
% 0.21/0.46  fof(f99,plain,(
% 0.21/0.46    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.21/0.46    inference(resolution,[],[f56,f48])).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    v2_funct_1(sK3)),
% 0.21/0.46    inference(cnf_transformation,[],[f39])).
% 0.21/0.46  fof(f56,plain,(
% 0.21/0.46    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(flattening,[],[f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.46  fof(f343,plain,(
% 0.21/0.46    k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | (spl4_4 | ~spl4_5)),
% 0.21/0.46    inference(forward_demodulation,[],[f342,f293])).
% 0.21/0.46  fof(f293,plain,(
% 0.21/0.46    k2_funct_1(sK3) = k2_tops_2(k1_relat_1(sK3),k2_relat_1(sK3),sK3) | ~spl4_5),
% 0.21/0.46    inference(backward_demodulation,[],[f161,f232])).
% 0.21/0.46  fof(f232,plain,(
% 0.21/0.46    k2_struct_0(sK1) = k1_relat_1(sK3) | ~spl4_5),
% 0.21/0.46    inference(superposition,[],[f70,f229])).
% 0.21/0.46  fof(f229,plain,(
% 0.21/0.46    k1_relat_1(sK3) = k2_relat_1(k6_partfun1(k2_struct_0(sK1))) | ~spl4_5),
% 0.21/0.46    inference(backward_demodulation,[],[f128,f223])).
% 0.21/0.46  fof(f223,plain,(
% 0.21/0.46    k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k2_struct_0(sK1)) | ~spl4_5),
% 0.21/0.46    inference(avatar_component_clause,[],[f221])).
% 0.21/0.46  fof(f221,plain,(
% 0.21/0.46    spl4_5 <=> k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k2_struct_0(sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.46  fof(f128,plain,(
% 0.21/0.46    k1_relat_1(sK3) = k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3)))),
% 0.21/0.46    inference(subsumption_resolution,[],[f127,f98])).
% 0.21/0.46  fof(f127,plain,(
% 0.21/0.46    k1_relat_1(sK3) = k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) | ~v1_relat_1(sK3)),
% 0.21/0.46    inference(subsumption_resolution,[],[f126,f44])).
% 0.21/0.46  fof(f126,plain,(
% 0.21/0.46    k1_relat_1(sK3) = k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.21/0.46    inference(resolution,[],[f59,f48])).
% 0.21/0.46  fof(f59,plain,(
% 0.21/0.46    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(flattening,[],[f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).
% 0.21/0.46  fof(f70,plain,(
% 0.21/0.46    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 0.21/0.46    inference(definition_unfolding,[],[f53,f51])).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,axiom,(
% 0.21/0.46    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.46  fof(f161,plain,(
% 0.21/0.46    k2_funct_1(sK3) = k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)),
% 0.21/0.46    inference(subsumption_resolution,[],[f160,f44])).
% 0.21/0.46  fof(f160,plain,(
% 0.21/0.46    k2_funct_1(sK3) = k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3) | ~v1_funct_1(sK3)),
% 0.21/0.46    inference(subsumption_resolution,[],[f159,f110])).
% 0.21/0.46  fof(f110,plain,(
% 0.21/0.46    v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3))),
% 0.21/0.46    inference(backward_demodulation,[],[f82,f107])).
% 0.21/0.46  fof(f107,plain,(
% 0.21/0.46    k2_struct_0(sK2) = k2_relat_1(sK3)),
% 0.21/0.46    inference(backward_demodulation,[],[f80,f106])).
% 0.21/0.46  fof(f106,plain,(
% 0.21/0.46    k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k2_relat_1(sK3)),
% 0.21/0.46    inference(resolution,[],[f62,f81])).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(ennf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.46  fof(f80,plain,(
% 0.21/0.46    k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3)),
% 0.21/0.46    inference(backward_demodulation,[],[f76,f73])).
% 0.21/0.46  fof(f76,plain,(
% 0.21/0.46    k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK2),sK3)),
% 0.21/0.46    inference(backward_demodulation,[],[f47,f72])).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),
% 0.21/0.46    inference(cnf_transformation,[],[f39])).
% 0.21/0.46  fof(f82,plain,(
% 0.21/0.46    v1_funct_2(sK3,k2_struct_0(sK1),k2_struct_0(sK2))),
% 0.21/0.46    inference(backward_demodulation,[],[f74,f73])).
% 0.21/0.46  fof(f74,plain,(
% 0.21/0.46    v1_funct_2(sK3,k2_struct_0(sK1),u1_struct_0(sK2))),
% 0.21/0.46    inference(backward_demodulation,[],[f45,f72])).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))),
% 0.21/0.46    inference(cnf_transformation,[],[f39])).
% 0.21/0.46  fof(f159,plain,(
% 0.21/0.46    k2_funct_1(sK3) = k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3) | ~v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) | ~v1_funct_1(sK3)),
% 0.21/0.46    inference(subsumption_resolution,[],[f158,f109])).
% 0.21/0.46  fof(f109,plain,(
% 0.21/0.46    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3))))),
% 0.21/0.46    inference(backward_demodulation,[],[f81,f107])).
% 0.21/0.46  fof(f158,plain,(
% 0.21/0.46    k2_funct_1(sK3) = k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) | ~v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) | ~v1_funct_1(sK3)),
% 0.21/0.46    inference(subsumption_resolution,[],[f157,f48])).
% 0.21/0.46  fof(f157,plain,(
% 0.21/0.46    ~v2_funct_1(sK3) | k2_funct_1(sK3) = k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) | ~v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) | ~v1_funct_1(sK3)),
% 0.21/0.46    inference(trivial_inequality_removal,[],[f154])).
% 0.21/0.46  fof(f154,plain,(
% 0.21/0.46    k2_relat_1(sK3) != k2_relat_1(sK3) | ~v2_funct_1(sK3) | k2_funct_1(sK3) = k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) | ~v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) | ~v1_funct_1(sK3)),
% 0.21/0.46    inference(superposition,[],[f67,f114])).
% 0.21/0.46  fof(f114,plain,(
% 0.21/0.46    k2_relat_1(sK3) = k2_relset_1(k2_struct_0(sK1),k2_relat_1(sK3),sK3)),
% 0.21/0.46    inference(backward_demodulation,[],[f106,f107])).
% 0.21/0.46  fof(f67,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f31])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.46    inference(flattening,[],[f30])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.46    inference(ennf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 0.21/0.46  fof(f342,plain,(
% 0.21/0.46    k2_relat_1(sK3) != k1_relat_1(k2_tops_2(k1_relat_1(sK3),k2_relat_1(sK3),sK3)) | (spl4_4 | ~spl4_5)),
% 0.21/0.46    inference(forward_demodulation,[],[f147,f232])).
% 0.21/0.46  fof(f147,plain,(
% 0.21/0.46    k2_relat_1(sK3) != k1_relat_1(k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)) | spl4_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f145])).
% 0.21/0.46  fof(f145,plain,(
% 0.21/0.46    spl4_4 <=> k2_relat_1(sK3) = k1_relat_1(k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.46  fof(f262,plain,(
% 0.21/0.46    ~spl4_6),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f261])).
% 0.21/0.46  fof(f261,plain,(
% 0.21/0.46    $false | ~spl4_6),
% 0.21/0.46    inference(subsumption_resolution,[],[f242,f50])).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    v1_xboole_0(k1_xboole_0)),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    v1_xboole_0(k1_xboole_0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.46  fof(f242,plain,(
% 0.21/0.46    ~v1_xboole_0(k1_xboole_0) | ~spl4_6),
% 0.21/0.46    inference(backward_demodulation,[],[f112,f227])).
% 0.21/0.46  fof(f227,plain,(
% 0.21/0.46    k1_xboole_0 = k2_relat_1(sK3) | ~spl4_6),
% 0.21/0.46    inference(avatar_component_clause,[],[f225])).
% 0.21/0.46  fof(f225,plain,(
% 0.21/0.46    spl4_6 <=> k1_xboole_0 = k2_relat_1(sK3)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.46  fof(f112,plain,(
% 0.21/0.46    ~v1_xboole_0(k2_relat_1(sK3))),
% 0.21/0.46    inference(backward_demodulation,[],[f88,f107])).
% 0.21/0.46  fof(f88,plain,(
% 0.21/0.46    ~v1_xboole_0(k2_struct_0(sK2))),
% 0.21/0.46    inference(subsumption_resolution,[],[f87,f42])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    ~v2_struct_0(sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f39])).
% 0.21/0.46  fof(f87,plain,(
% 0.21/0.46    ~v1_xboole_0(k2_struct_0(sK2)) | v2_struct_0(sK2)),
% 0.21/0.46    inference(subsumption_resolution,[],[f85,f43])).
% 0.21/0.46  fof(f85,plain,(
% 0.21/0.46    ~v1_xboole_0(k2_struct_0(sK2)) | ~l1_struct_0(sK2) | v2_struct_0(sK2)),
% 0.21/0.46    inference(superposition,[],[f55,f73])).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,axiom,(
% 0.21/0.46    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.46  fof(f236,plain,(
% 0.21/0.46    spl4_3 | ~spl4_5),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f235])).
% 0.21/0.46  fof(f235,plain,(
% 0.21/0.46    $false | (spl4_3 | ~spl4_5)),
% 0.21/0.46    inference(subsumption_resolution,[],[f232,f168])).
% 0.21/0.46  fof(f168,plain,(
% 0.21/0.46    k2_struct_0(sK1) != k1_relat_1(sK3) | spl4_3),
% 0.21/0.46    inference(forward_demodulation,[],[f164,f104])).
% 0.21/0.46  fof(f104,plain,(
% 0.21/0.46    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))),
% 0.21/0.46    inference(subsumption_resolution,[],[f103,f98])).
% 0.21/0.46  fof(f103,plain,(
% 0.21/0.46    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3)),
% 0.21/0.46    inference(subsumption_resolution,[],[f102,f44])).
% 0.21/0.46  fof(f102,plain,(
% 0.21/0.46    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.21/0.46    inference(resolution,[],[f57,f48])).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f22])).
% 0.21/0.46  fof(f164,plain,(
% 0.21/0.46    k2_struct_0(sK1) != k2_relat_1(k2_funct_1(sK3)) | spl4_3),
% 0.21/0.46    inference(backward_demodulation,[],[f149,f161])).
% 0.21/0.46  fof(f149,plain,(
% 0.21/0.46    k2_struct_0(sK1) != k2_relat_1(k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)) | spl4_3),
% 0.21/0.46    inference(superposition,[],[f143,f135])).
% 0.21/0.46  fof(f135,plain,(
% 0.21/0.46    k2_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)) = k2_relat_1(k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3))),
% 0.21/0.46    inference(resolution,[],[f120,f132])).
% 0.21/0.46  fof(f132,plain,(
% 0.21/0.46    sP0(k2_struct_0(sK1),k2_relat_1(sK3),sK3)),
% 0.21/0.46    inference(subsumption_resolution,[],[f131,f44])).
% 0.21/0.46  fof(f131,plain,(
% 0.21/0.46    sP0(k2_struct_0(sK1),k2_relat_1(sK3),sK3) | ~v1_funct_1(sK3)),
% 0.21/0.46    inference(subsumption_resolution,[],[f129,f110])).
% 0.21/0.46  fof(f129,plain,(
% 0.21/0.46    sP0(k2_struct_0(sK1),k2_relat_1(sK3),sK3) | ~v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) | ~v1_funct_1(sK3)),
% 0.21/0.46    inference(resolution,[],[f66,f109])).
% 0.21/0.46  fof(f66,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X1,X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f35])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (sP0(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.46    inference(definition_folding,[],[f29,f34])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~sP0(X0,X1,X2))),
% 0.21/0.46    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.46    inference(flattening,[],[f28])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.46    inference(ennf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).
% 0.21/0.46  fof(f120,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | k2_relset_1(X1,X0,k2_tops_2(X0,X1,X2)) = k2_relat_1(k2_tops_2(X0,X1,X2))) )),
% 0.21/0.46    inference(resolution,[],[f65,f62])).
% 0.21/0.46  fof(f65,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~sP0(X0,X1,X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f40])).
% 0.21/0.46  % (21320)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~sP0(X0,X1,X2))),
% 0.21/0.46    inference(nnf_transformation,[],[f34])).
% 0.21/0.46  fof(f143,plain,(
% 0.21/0.46    k2_struct_0(sK1) != k2_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)) | spl4_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f141])).
% 0.21/0.46  fof(f141,plain,(
% 0.21/0.46    spl4_3 <=> k2_struct_0(sK1) = k2_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.46  fof(f228,plain,(
% 0.21/0.46    spl4_5 | spl4_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f219,f225,f221])).
% 0.21/0.46  % (21319)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  fof(f219,plain,(
% 0.21/0.46    k1_xboole_0 = k2_relat_1(sK3) | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k2_struct_0(sK1))),
% 0.21/0.46    inference(subsumption_resolution,[],[f218,f44])).
% 0.21/0.46  fof(f218,plain,(
% 0.21/0.46    k1_xboole_0 = k2_relat_1(sK3) | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k2_struct_0(sK1)) | ~v1_funct_1(sK3)),
% 0.21/0.46    inference(subsumption_resolution,[],[f217,f110])).
% 0.21/0.46  fof(f217,plain,(
% 0.21/0.46    k1_xboole_0 = k2_relat_1(sK3) | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k2_struct_0(sK1)) | ~v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) | ~v1_funct_1(sK3)),
% 0.21/0.46    inference(subsumption_resolution,[],[f216,f109])).
% 0.21/0.46  fof(f216,plain,(
% 0.21/0.46    k1_xboole_0 = k2_relat_1(sK3) | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k2_struct_0(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) | ~v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) | ~v1_funct_1(sK3)),
% 0.21/0.46    inference(subsumption_resolution,[],[f215,f48])).
% 0.21/0.46  fof(f215,plain,(
% 0.21/0.46    k1_xboole_0 = k2_relat_1(sK3) | ~v2_funct_1(sK3) | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k2_struct_0(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) | ~v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) | ~v1_funct_1(sK3)),
% 0.21/0.46    inference(trivial_inequality_removal,[],[f211])).
% 0.21/0.46  fof(f211,plain,(
% 0.21/0.46    k2_relat_1(sK3) != k2_relat_1(sK3) | k1_xboole_0 = k2_relat_1(sK3) | ~v2_funct_1(sK3) | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k2_struct_0(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) | ~v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) | ~v1_funct_1(sK3)),
% 0.21/0.46    inference(superposition,[],[f68,f114])).
% 0.21/0.46  fof(f68,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f33])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.46    inference(flattening,[],[f32])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.46    inference(ennf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 0.21/0.46  fof(f148,plain,(
% 0.21/0.46    ~spl4_3 | ~spl4_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f139,f145,f141])).
% 0.21/0.46  % (21326)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.46  fof(f139,plain,(
% 0.21/0.46    k2_relat_1(sK3) != k1_relat_1(k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)) | k2_struct_0(sK1) != k2_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3))),
% 0.21/0.46    inference(backward_demodulation,[],[f115,f137])).
% 0.21/0.46  fof(f137,plain,(
% 0.21/0.46    k1_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)) = k1_relat_1(k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3))),
% 0.21/0.46    inference(resolution,[],[f121,f132])).
% 0.21/0.46  % (21325)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.46  fof(f121,plain,(
% 0.21/0.46    ( ! [X4,X5,X3] : (~sP0(X3,X4,X5) | k1_relset_1(X4,X3,k2_tops_2(X3,X4,X5)) = k1_relat_1(k2_tops_2(X3,X4,X5))) )),
% 0.21/0.46    inference(resolution,[],[f65,f61])).
% 0.21/0.46  fof(f61,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f26])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.46  fof(f115,plain,(
% 0.21/0.46    k2_struct_0(sK1) != k2_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)) | k2_relat_1(sK3) != k1_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3))),
% 0.21/0.46    inference(forward_demodulation,[],[f111,f107])).
% 0.21/0.46  fof(f111,plain,(
% 0.21/0.46    k2_relat_1(sK3) != k1_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3))),
% 0.21/0.46    inference(backward_demodulation,[],[f83,f107])).
% 0.21/0.46  fof(f83,plain,(
% 0.21/0.46    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) | k2_struct_0(sK2) != k1_relset_1(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3))),
% 0.21/0.46    inference(forward_demodulation,[],[f79,f73])).
% 0.21/0.46  fof(f79,plain,(
% 0.21/0.46    k2_struct_0(sK2) != k1_relset_1(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK2),sK3))),
% 0.21/0.46    inference(backward_demodulation,[],[f78,f73])).
% 0.21/0.46  fof(f78,plain,(
% 0.21/0.46    k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK2),sK3)) | k2_struct_0(sK2) != k1_relset_1(u1_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK2),sK3))),
% 0.21/0.46    inference(forward_demodulation,[],[f77,f72])).
% 0.21/0.46  fof(f77,plain,(
% 0.21/0.46    k2_struct_0(sK2) != k1_relset_1(u1_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK2),sK3)) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))),
% 0.21/0.46    inference(backward_demodulation,[],[f49,f72])).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) | k2_struct_0(sK2) != k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))),
% 0.21/0.46    inference(cnf_transformation,[],[f39])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (21323)------------------------------
% 0.21/0.46  % (21323)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (21323)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (21323)Memory used [KB]: 10874
% 0.21/0.46  % (21323)Time elapsed: 0.049 s
% 0.21/0.46  % (21323)------------------------------
% 0.21/0.46  % (21323)------------------------------
% 0.21/0.46  % (21313)Success in time 0.112 s
%------------------------------------------------------------------------------
