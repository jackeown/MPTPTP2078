%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:50 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :  199 (1239 expanded)
%              Number of leaves         :   26 ( 391 expanded)
%              Depth                    :   25
%              Number of atoms          :  758 (11417 expanded)
%              Number of equality atoms :  193 (3832 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f890,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f221,f247,f278,f304,f324,f383,f889])).

fof(f889,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f888])).

fof(f888,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f887,f68])).

fof(f68,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f53,f52])).

fof(f52,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_funct_1(X2) != X3
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0
            & v2_funct_1(X2)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & k2_relset_1(X0,X1,X2) = X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & sK1 = k2_relset_1(sK0,sK1,sK2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ? [X3] :
        ( k2_funct_1(sK2) != X3
        & k1_xboole_0 != sK1
        & k1_xboole_0 != sK0
        & v2_funct_1(sK2)
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & sK1 = k2_relset_1(sK0,sK1,sK2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( k2_funct_1(sK2) != sK3
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & v2_funct_1(sK2)
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

fof(f887,plain,
    ( k2_funct_1(sK2) = sK3
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f737,f883])).

fof(f883,plain,
    ( sK3 = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f882,f747])).

fof(f747,plain,
    ( sK3 = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f136,f721])).

fof(f721,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f709,f192])).

fof(f192,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f116,f63])).

fof(f63,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f116,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f59,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f59,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f54])).

fof(f709,plain,
    ( k2_relat_1(sK2) = k1_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f336,f706])).

fof(f706,plain,
    ( sK2 = k2_funct_1(sK3)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f705,f202])).

fof(f202,plain,(
    sK2 = k5_relat_1(sK2,k6_partfun1(sK1)) ),
    inference(forward_demodulation,[],[f130,f192])).

fof(f130,plain,(
    sK2 = k5_relat_1(sK2,k6_partfun1(k2_relat_1(sK2))) ),
    inference(resolution,[],[f122,f104])).

fof(f104,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ) ),
    inference(definition_unfolding,[],[f91,f84])).

fof(f84,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f91,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f122,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f119,f96])).

fof(f96,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f119,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f59,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f705,plain,
    ( k2_funct_1(sK3) = k5_relat_1(sK2,k6_partfun1(sK1))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f704,f390])).

fof(f390,plain,
    ( k2_funct_1(sK3) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3))
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f385,f334])).

fof(f334,plain,
    ( sK0 = k1_relat_1(k2_funct_1(sK3))
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f333,f195])).

fof(f195,plain,(
    sK0 = k2_relat_1(sK3) ),
    inference(forward_demodulation,[],[f123,f169])).

fof(f169,plain,(
    sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f168,f60])).

fof(f60,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f168,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f167,f61])).

fof(f61,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f167,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f166,f62])).

fof(f62,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f54])).

fof(f166,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f165,f57])).

fof(f57,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f165,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f164,f58])).

fof(f58,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f164,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f162,f59])).

fof(f162,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f64,f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

fof(f64,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f54])).

fof(f123,plain,(
    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f62,f88])).

fof(f333,plain,
    ( k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f332,f129])).

fof(f129,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f126,f96])).

fof(f126,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(resolution,[],[f62,f94])).

fof(f332,plain,
    ( k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f330,f60])).

fof(f330,plain,
    ( k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_2 ),
    inference(resolution,[],[f219,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f219,plain,
    ( v2_funct_1(sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl4_2
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f385,plain,
    ( k2_funct_1(sK3) = k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK3))),k2_funct_1(sK3))
    | ~ spl4_7 ),
    inference(resolution,[],[f374,f103])).

fof(f103,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(definition_unfolding,[],[f90,f84])).

fof(f90,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

fof(f374,plain,
    ( v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f373])).

fof(f373,plain,
    ( spl4_7
  <=> v1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f704,plain,
    ( k5_relat_1(sK2,k6_partfun1(sK1)) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3))
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f700,f216])).

fof(f216,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f214])).

fof(f214,plain,
    ( spl4_1
  <=> k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f700,plain,
    ( k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) = k5_relat_1(sK2,k5_relat_1(sK3,k2_funct_1(sK3)))
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(resolution,[],[f538,f374])).

fof(f538,plain,
    ( ! [X13] :
        ( ~ v1_relat_1(X13)
        | k5_relat_1(sK2,k5_relat_1(sK3,X13)) = k5_relat_1(k6_partfun1(sK0),X13) )
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f535,f316])).

fof(f316,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f212,f277])).

fof(f277,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f275])).

fof(f275,plain,
    ( spl4_6
  <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f212,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f209,f60])).

fof(f209,plain,
    ( ~ v1_funct_1(sK3)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f120,f62])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | k1_partfun1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f117,f57])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | k1_partfun1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f59,f87])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f535,plain,(
    ! [X13] :
      ( ~ v1_relat_1(X13)
      | k5_relat_1(k5_relat_1(sK2,sK3),X13) = k5_relat_1(sK2,k5_relat_1(sK3,X13)) ) ),
    inference(resolution,[],[f132,f129])).

fof(f132,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k5_relat_1(k5_relat_1(sK2,X1),X0) = k5_relat_1(sK2,k5_relat_1(X1,X0)) ) ),
    inference(resolution,[],[f122,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
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
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f336,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f335,f129])).

fof(f335,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f331,f60])).

fof(f331,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_2 ),
    inference(resolution,[],[f219,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f136,plain,(
    sK3 = k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) ),
    inference(resolution,[],[f129,f103])).

fof(f882,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f878,f160])).

fof(f160,plain,(
    k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(subsumption_resolution,[],[f159,f57])).

fof(f159,plain,
    ( k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f158,f58])).

fof(f158,plain,
    ( k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f157,f59])).

fof(f157,plain,
    ( k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f156,f65])).

fof(f65,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f156,plain,
    ( ~ v2_funct_1(sK2)
    | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f144,f67])).

fof(f67,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f54])).

fof(f144,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(trivial_inequality_removal,[],[f143])).

fof(f143,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f70,f63])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

fof(f878,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),sK3)
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(resolution,[],[f564,f231])).

fof(f231,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f230])).

fof(f230,plain,
    ( spl4_3
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f564,plain,
    ( ! [X13] :
        ( ~ v1_relat_1(X13)
        | k5_relat_1(k5_relat_1(X13,sK2),sK3) = k5_relat_1(X13,k6_partfun1(sK0)) )
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f551,f316])).

fof(f551,plain,(
    ! [X13] :
      ( ~ v1_relat_1(X13)
      | k5_relat_1(k5_relat_1(X13,sK2),sK3) = k5_relat_1(X13,k5_relat_1(sK2,sK3)) ) ),
    inference(resolution,[],[f133,f129])).

fof(f133,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3)
      | k5_relat_1(k5_relat_1(X3,sK2),X2) = k5_relat_1(X3,k5_relat_1(sK2,X2)) ) ),
    inference(resolution,[],[f122,f89])).

fof(f737,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f253,f708])).

fof(f708,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f334,f706])).

fof(f253,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(k1_relat_1(sK2)))
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f248,f203])).

fof(f203,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f115,f122])).

fof(f115,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f113,f57])).

fof(f113,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f65,f72])).

fof(f248,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2))))
    | ~ spl4_3 ),
    inference(resolution,[],[f231,f104])).

fof(f383,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f382])).

fof(f382,plain,
    ( $false
    | spl4_7 ),
    inference(subsumption_resolution,[],[f381,f129])).

fof(f381,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_7 ),
    inference(subsumption_resolution,[],[f380,f60])).

fof(f380,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl4_7 ),
    inference(resolution,[],[f375,f73])).

fof(f73,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f375,plain,
    ( ~ v1_relat_1(k2_funct_1(sK3))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f373])).

fof(f324,plain,
    ( spl4_2
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f323])).

fof(f323,plain,
    ( $false
    | spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f322,f101])).

fof(f101,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f80,f84])).

fof(f80,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f322,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl4_2
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f321,f277])).

fof(f321,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | spl4_2 ),
    inference(subsumption_resolution,[],[f320,f60])).

fof(f320,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | ~ v1_funct_1(sK3)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f319,f66])).

fof(f66,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f54])).

fof(f319,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK3)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f318,f62])).

fof(f318,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK3)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f317,f220])).

fof(f220,plain,
    ( ~ v2_funct_1(sK3)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f218])).

fof(f317,plain,
    ( v2_funct_1(sK3)
    | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f150,f61])).

fof(f150,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_2(X3,sK1,X2)
      | v2_funct_1(X3)
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
      | k1_xboole_0 = X2
      | ~ v1_funct_1(X3) ) ),
    inference(subsumption_resolution,[],[f149,f57])).

fof(f149,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
      | ~ v1_funct_2(X3,sK1,X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f148,f58])).

fof(f148,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
      | ~ v1_funct_2(X3,sK1,X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f146,f59])).

fof(f146,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
      | ~ v1_funct_2(X3,sK1,X2)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(trivial_inequality_removal,[],[f141])).

fof(f141,plain,(
    ! [X2,X3] :
      ( sK1 != sK1
      | k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
      | ~ v1_funct_2(X3,sK1,X2)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(superposition,[],[f77,f63])).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X3) != X1
      | k1_xboole_0 = X2
      | v2_funct_1(X4)
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( k2_relset_1(X0,X1,X3) = X1
              & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) )
           => ( ( v2_funct_1(X4)
                & v2_funct_1(X3) )
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).

fof(f304,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f303])).

fof(f303,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f302,f57])).

fof(f302,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_5 ),
    inference(subsumption_resolution,[],[f301,f59])).

fof(f301,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl4_5 ),
    inference(subsumption_resolution,[],[f300,f60])).

fof(f300,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl4_5 ),
    inference(subsumption_resolution,[],[f299,f62])).

fof(f299,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl4_5 ),
    inference(resolution,[],[f273,f86])).

fof(f86,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f273,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f271])).

fof(f271,plain,
    ( spl4_5
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f278,plain,
    ( ~ spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f163,f275,f271])).

fof(f163,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f161,f107])).

fof(f107,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f95,f84])).

fof(f95,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f161,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f64,f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f247,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f246])).

fof(f246,plain,
    ( $false
    | spl4_3 ),
    inference(subsumption_resolution,[],[f245,f122])).

fof(f245,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_3 ),
    inference(subsumption_resolution,[],[f244,f57])).

fof(f244,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_3 ),
    inference(resolution,[],[f232,f73])).

fof(f232,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f230])).

fof(f221,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f187,f218,f214])).

fof(f187,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f186,f60])).

fof(f186,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f185,f61])).

fof(f185,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f184,f62])).

fof(f184,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f175,f66])).

fof(f175,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(trivial_inequality_removal,[],[f172])).

fof(f172,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(superposition,[],[f69,f169])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:45:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (32195)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (32194)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  % (32196)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (32201)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.25/0.53  % (32221)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.25/0.53  % (32193)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.25/0.53  % (32211)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.25/0.53  % (32206)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.25/0.53  % (32197)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.25/0.53  % (32215)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.25/0.53  % (32200)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.25/0.53  % (32207)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.25/0.54  % (32202)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.25/0.54  % (32217)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.25/0.54  % (32203)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.25/0.54  % (32198)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.25/0.54  % (32210)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.25/0.54  % (32219)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.25/0.54  % (32214)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.25/0.54  % (32199)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.25/0.54  % (32204)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.44/0.55  % (32222)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.44/0.55  % (32218)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.44/0.55  % (32209)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.44/0.55  % (32209)Refutation not found, incomplete strategy% (32209)------------------------------
% 1.44/0.55  % (32209)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (32209)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.55  
% 1.44/0.55  % (32209)Memory used [KB]: 10746
% 1.44/0.55  % (32209)Time elapsed: 0.147 s
% 1.44/0.55  % (32209)------------------------------
% 1.44/0.55  % (32209)------------------------------
% 1.44/0.55  % (32213)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.44/0.55  % (32216)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.44/0.55  % (32205)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.44/0.55  % (32208)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.44/0.56  % (32220)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.44/0.57  % (32212)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.44/0.60  % (32217)Refutation found. Thanks to Tanya!
% 1.44/0.60  % SZS status Theorem for theBenchmark
% 1.44/0.61  % SZS output start Proof for theBenchmark
% 1.44/0.61  fof(f890,plain,(
% 1.44/0.61    $false),
% 1.44/0.61    inference(avatar_sat_refutation,[],[f221,f247,f278,f304,f324,f383,f889])).
% 1.44/0.61  fof(f889,plain,(
% 1.44/0.61    ~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_6 | ~spl4_7),
% 1.44/0.61    inference(avatar_contradiction_clause,[],[f888])).
% 1.44/0.61  fof(f888,plain,(
% 1.44/0.61    $false | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_6 | ~spl4_7)),
% 1.44/0.61    inference(subsumption_resolution,[],[f887,f68])).
% 1.44/0.61  fof(f68,plain,(
% 1.44/0.61    k2_funct_1(sK2) != sK3),
% 1.44/0.61    inference(cnf_transformation,[],[f54])).
% 1.44/0.61  fof(f54,plain,(
% 1.44/0.61    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.44/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f53,f52])).
% 1.44/0.61  fof(f52,plain,(
% 1.44/0.61    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.44/0.61    introduced(choice_axiom,[])).
% 1.44/0.61  fof(f53,plain,(
% 1.44/0.61    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.44/0.61    introduced(choice_axiom,[])).
% 1.44/0.61  fof(f26,plain,(
% 1.44/0.61    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.44/0.61    inference(flattening,[],[f25])).
% 1.44/0.61  fof(f25,plain,(
% 1.44/0.61    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.44/0.61    inference(ennf_transformation,[],[f23])).
% 1.44/0.61  fof(f23,negated_conjecture,(
% 1.44/0.61    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.44/0.61    inference(negated_conjecture,[],[f22])).
% 1.44/0.61  fof(f22,conjecture,(
% 1.44/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.44/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 1.44/0.61  fof(f887,plain,(
% 1.44/0.61    k2_funct_1(sK2) = sK3 | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_6 | ~spl4_7)),
% 1.44/0.61    inference(backward_demodulation,[],[f737,f883])).
% 1.44/0.61  fof(f883,plain,(
% 1.44/0.61    sK3 = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_6 | ~spl4_7)),
% 1.44/0.61    inference(forward_demodulation,[],[f882,f747])).
% 1.44/0.61  fof(f747,plain,(
% 1.44/0.61    sK3 = k5_relat_1(k6_partfun1(sK1),sK3) | (~spl4_1 | ~spl4_2 | ~spl4_6 | ~spl4_7)),
% 1.44/0.61    inference(backward_demodulation,[],[f136,f721])).
% 1.44/0.61  fof(f721,plain,(
% 1.44/0.61    sK1 = k1_relat_1(sK3) | (~spl4_1 | ~spl4_2 | ~spl4_6 | ~spl4_7)),
% 1.44/0.61    inference(forward_demodulation,[],[f709,f192])).
% 1.44/0.61  fof(f192,plain,(
% 1.44/0.61    sK1 = k2_relat_1(sK2)),
% 1.44/0.61    inference(forward_demodulation,[],[f116,f63])).
% 1.44/0.61  fof(f63,plain,(
% 1.44/0.61    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.44/0.61    inference(cnf_transformation,[],[f54])).
% 1.44/0.61  fof(f116,plain,(
% 1.44/0.61    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 1.44/0.61    inference(resolution,[],[f59,f88])).
% 1.44/0.61  fof(f88,plain,(
% 1.44/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.44/0.61    inference(cnf_transformation,[],[f43])).
% 1.44/0.61  fof(f43,plain,(
% 1.44/0.61    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.61    inference(ennf_transformation,[],[f13])).
% 1.44/0.61  fof(f13,axiom,(
% 1.44/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.44/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.44/0.61  fof(f59,plain,(
% 1.44/0.61    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.44/0.61    inference(cnf_transformation,[],[f54])).
% 1.44/0.61  fof(f709,plain,(
% 1.44/0.61    k2_relat_1(sK2) = k1_relat_1(sK3) | (~spl4_1 | ~spl4_2 | ~spl4_6 | ~spl4_7)),
% 1.44/0.61    inference(backward_demodulation,[],[f336,f706])).
% 1.44/0.61  fof(f706,plain,(
% 1.44/0.61    sK2 = k2_funct_1(sK3) | (~spl4_1 | ~spl4_2 | ~spl4_6 | ~spl4_7)),
% 1.44/0.61    inference(forward_demodulation,[],[f705,f202])).
% 1.44/0.61  fof(f202,plain,(
% 1.44/0.61    sK2 = k5_relat_1(sK2,k6_partfun1(sK1))),
% 1.44/0.61    inference(forward_demodulation,[],[f130,f192])).
% 1.44/0.61  fof(f130,plain,(
% 1.44/0.61    sK2 = k5_relat_1(sK2,k6_partfun1(k2_relat_1(sK2)))),
% 1.44/0.61    inference(resolution,[],[f122,f104])).
% 1.44/0.61  fof(f104,plain,(
% 1.44/0.61    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0) )),
% 1.44/0.61    inference(definition_unfolding,[],[f91,f84])).
% 1.44/0.61  fof(f84,plain,(
% 1.44/0.61    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.44/0.61    inference(cnf_transformation,[],[f18])).
% 1.44/0.61  fof(f18,axiom,(
% 1.44/0.61    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.44/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.44/0.61  fof(f91,plain,(
% 1.44/0.61    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 1.44/0.61    inference(cnf_transformation,[],[f46])).
% 1.44/0.61  fof(f46,plain,(
% 1.44/0.61    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.44/0.61    inference(ennf_transformation,[],[f8])).
% 1.44/0.61  fof(f8,axiom,(
% 1.44/0.61    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 1.44/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 1.44/0.61  fof(f122,plain,(
% 1.44/0.61    v1_relat_1(sK2)),
% 1.44/0.61    inference(subsumption_resolution,[],[f119,f96])).
% 1.44/0.61  fof(f96,plain,(
% 1.44/0.61    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.44/0.61    inference(cnf_transformation,[],[f3])).
% 1.44/0.61  fof(f3,axiom,(
% 1.44/0.61    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.44/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.44/0.61  fof(f119,plain,(
% 1.44/0.61    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.44/0.61    inference(resolution,[],[f59,f94])).
% 1.44/0.61  fof(f94,plain,(
% 1.44/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.44/0.61    inference(cnf_transformation,[],[f47])).
% 1.44/0.61  fof(f47,plain,(
% 1.44/0.61    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.44/0.61    inference(ennf_transformation,[],[f1])).
% 1.44/0.61  fof(f1,axiom,(
% 1.44/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.44/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.44/0.61  fof(f705,plain,(
% 1.44/0.61    k2_funct_1(sK3) = k5_relat_1(sK2,k6_partfun1(sK1)) | (~spl4_1 | ~spl4_2 | ~spl4_6 | ~spl4_7)),
% 1.44/0.61    inference(forward_demodulation,[],[f704,f390])).
% 1.44/0.61  fof(f390,plain,(
% 1.44/0.61    k2_funct_1(sK3) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) | (~spl4_2 | ~spl4_7)),
% 1.44/0.61    inference(forward_demodulation,[],[f385,f334])).
% 1.44/0.61  fof(f334,plain,(
% 1.44/0.61    sK0 = k1_relat_1(k2_funct_1(sK3)) | ~spl4_2),
% 1.44/0.61    inference(forward_demodulation,[],[f333,f195])).
% 1.44/0.61  fof(f195,plain,(
% 1.44/0.61    sK0 = k2_relat_1(sK3)),
% 1.44/0.61    inference(forward_demodulation,[],[f123,f169])).
% 1.44/0.61  fof(f169,plain,(
% 1.44/0.61    sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.44/0.61    inference(subsumption_resolution,[],[f168,f60])).
% 1.44/0.61  fof(f60,plain,(
% 1.44/0.61    v1_funct_1(sK3)),
% 1.44/0.61    inference(cnf_transformation,[],[f54])).
% 1.44/0.61  fof(f168,plain,(
% 1.44/0.61    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK3)),
% 1.44/0.61    inference(subsumption_resolution,[],[f167,f61])).
% 1.44/0.61  fof(f61,plain,(
% 1.44/0.61    v1_funct_2(sK3,sK1,sK0)),
% 1.44/0.61    inference(cnf_transformation,[],[f54])).
% 1.44/0.61  fof(f167,plain,(
% 1.44/0.61    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.44/0.61    inference(subsumption_resolution,[],[f166,f62])).
% 1.44/0.61  fof(f62,plain,(
% 1.44/0.61    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.44/0.61    inference(cnf_transformation,[],[f54])).
% 1.44/0.61  fof(f166,plain,(
% 1.44/0.61    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.44/0.61    inference(subsumption_resolution,[],[f165,f57])).
% 1.44/0.61  fof(f57,plain,(
% 1.44/0.61    v1_funct_1(sK2)),
% 1.44/0.61    inference(cnf_transformation,[],[f54])).
% 1.44/0.61  fof(f165,plain,(
% 1.44/0.61    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.44/0.61    inference(subsumption_resolution,[],[f164,f58])).
% 1.44/0.61  fof(f58,plain,(
% 1.44/0.61    v1_funct_2(sK2,sK0,sK1)),
% 1.44/0.61    inference(cnf_transformation,[],[f54])).
% 1.44/0.61  fof(f164,plain,(
% 1.44/0.61    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.44/0.61    inference(subsumption_resolution,[],[f162,f59])).
% 1.44/0.61  fof(f162,plain,(
% 1.44/0.61    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.44/0.61    inference(resolution,[],[f64,f83])).
% 1.44/0.61  fof(f83,plain,(
% 1.44/0.61    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.44/0.61    inference(cnf_transformation,[],[f38])).
% 1.44/0.61  fof(f38,plain,(
% 1.44/0.61    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.44/0.61    inference(flattening,[],[f37])).
% 1.44/0.61  fof(f37,plain,(
% 1.44/0.61    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.44/0.61    inference(ennf_transformation,[],[f19])).
% 1.44/0.61  fof(f19,axiom,(
% 1.44/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.44/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
% 1.44/0.61  fof(f64,plain,(
% 1.44/0.61    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.44/0.61    inference(cnf_transformation,[],[f54])).
% 1.44/0.61  fof(f123,plain,(
% 1.44/0.61    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3)),
% 1.44/0.61    inference(resolution,[],[f62,f88])).
% 1.44/0.61  fof(f333,plain,(
% 1.44/0.61    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) | ~spl4_2),
% 1.44/0.61    inference(subsumption_resolution,[],[f332,f129])).
% 1.44/0.61  fof(f129,plain,(
% 1.44/0.61    v1_relat_1(sK3)),
% 1.44/0.61    inference(subsumption_resolution,[],[f126,f96])).
% 1.44/0.61  fof(f126,plain,(
% 1.44/0.61    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 1.44/0.61    inference(resolution,[],[f62,f94])).
% 1.44/0.61  fof(f332,plain,(
% 1.44/0.61    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3) | ~spl4_2),
% 1.44/0.61    inference(subsumption_resolution,[],[f330,f60])).
% 1.44/0.61  fof(f330,plain,(
% 1.44/0.61    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_2),
% 1.44/0.61    inference(resolution,[],[f219,f71])).
% 1.44/0.62  fof(f71,plain,(
% 1.44/0.62    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.44/0.62    inference(cnf_transformation,[],[f30])).
% 1.44/0.62  fof(f30,plain,(
% 1.44/0.62    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.44/0.62    inference(flattening,[],[f29])).
% 1.44/0.62  fof(f29,plain,(
% 1.44/0.62    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.44/0.62    inference(ennf_transformation,[],[f11])).
% 1.44/0.62  fof(f11,axiom,(
% 1.44/0.62    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.44/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 1.44/0.62  fof(f219,plain,(
% 1.44/0.62    v2_funct_1(sK3) | ~spl4_2),
% 1.44/0.62    inference(avatar_component_clause,[],[f218])).
% 1.44/0.62  fof(f218,plain,(
% 1.44/0.62    spl4_2 <=> v2_funct_1(sK3)),
% 1.44/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.44/0.63  fof(f385,plain,(
% 1.44/0.63    k2_funct_1(sK3) = k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK3))),k2_funct_1(sK3)) | ~spl4_7),
% 1.44/0.63    inference(resolution,[],[f374,f103])).
% 1.44/0.63  fof(f103,plain,(
% 1.44/0.63    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0) )),
% 1.44/0.63    inference(definition_unfolding,[],[f90,f84])).
% 1.44/0.63  fof(f90,plain,(
% 1.44/0.63    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 1.44/0.63    inference(cnf_transformation,[],[f45])).
% 1.44/0.63  fof(f45,plain,(
% 1.44/0.63    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 1.44/0.63    inference(ennf_transformation,[],[f7])).
% 1.44/0.63  fof(f7,axiom,(
% 1.44/0.63    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 1.44/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).
% 1.44/0.63  fof(f374,plain,(
% 1.44/0.63    v1_relat_1(k2_funct_1(sK3)) | ~spl4_7),
% 1.44/0.63    inference(avatar_component_clause,[],[f373])).
% 1.44/0.63  fof(f373,plain,(
% 1.44/0.63    spl4_7 <=> v1_relat_1(k2_funct_1(sK3))),
% 1.44/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.44/0.63  fof(f704,plain,(
% 1.44/0.63    k5_relat_1(sK2,k6_partfun1(sK1)) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) | (~spl4_1 | ~spl4_6 | ~spl4_7)),
% 1.44/0.63    inference(forward_demodulation,[],[f700,f216])).
% 1.44/0.63  fof(f216,plain,(
% 1.44/0.63    k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl4_1),
% 1.44/0.63    inference(avatar_component_clause,[],[f214])).
% 1.44/0.63  fof(f214,plain,(
% 1.44/0.63    spl4_1 <=> k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 1.44/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.44/0.63  fof(f700,plain,(
% 1.44/0.63    k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) = k5_relat_1(sK2,k5_relat_1(sK3,k2_funct_1(sK3))) | (~spl4_6 | ~spl4_7)),
% 1.44/0.63    inference(resolution,[],[f538,f374])).
% 1.44/0.63  fof(f538,plain,(
% 1.44/0.63    ( ! [X13] : (~v1_relat_1(X13) | k5_relat_1(sK2,k5_relat_1(sK3,X13)) = k5_relat_1(k6_partfun1(sK0),X13)) ) | ~spl4_6),
% 1.44/0.63    inference(forward_demodulation,[],[f535,f316])).
% 1.44/0.63  fof(f316,plain,(
% 1.44/0.63    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_6),
% 1.44/0.63    inference(forward_demodulation,[],[f212,f277])).
% 1.44/0.63  fof(f277,plain,(
% 1.44/0.63    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~spl4_6),
% 1.44/0.63    inference(avatar_component_clause,[],[f275])).
% 1.44/0.63  fof(f275,plain,(
% 1.44/0.63    spl4_6 <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)),
% 1.44/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.44/0.63  fof(f212,plain,(
% 1.44/0.63    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 1.44/0.63    inference(subsumption_resolution,[],[f209,f60])).
% 1.44/0.63  fof(f209,plain,(
% 1.44/0.63    ~v1_funct_1(sK3) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 1.44/0.63    inference(resolution,[],[f120,f62])).
% 1.44/0.63  fof(f120,plain,(
% 1.44/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | k1_partfun1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0)) )),
% 1.44/0.63    inference(subsumption_resolution,[],[f117,f57])).
% 1.44/0.63  fof(f117,plain,(
% 1.44/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | k1_partfun1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0) | ~v1_funct_1(sK2)) )),
% 1.44/0.63    inference(resolution,[],[f59,f87])).
% 1.44/0.63  fof(f87,plain,(
% 1.44/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X4)) )),
% 1.44/0.63    inference(cnf_transformation,[],[f42])).
% 1.44/0.63  fof(f42,plain,(
% 1.44/0.63    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.44/0.63    inference(flattening,[],[f41])).
% 1.44/0.63  fof(f41,plain,(
% 1.44/0.63    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.44/0.63    inference(ennf_transformation,[],[f17])).
% 1.44/0.63  fof(f17,axiom,(
% 1.44/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.44/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.44/0.63  fof(f535,plain,(
% 1.44/0.63    ( ! [X13] : (~v1_relat_1(X13) | k5_relat_1(k5_relat_1(sK2,sK3),X13) = k5_relat_1(sK2,k5_relat_1(sK3,X13))) )),
% 1.44/0.63    inference(resolution,[],[f132,f129])).
% 1.44/0.63  fof(f132,plain,(
% 1.44/0.63    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k5_relat_1(k5_relat_1(sK2,X1),X0) = k5_relat_1(sK2,k5_relat_1(X1,X0))) )),
% 1.44/0.63    inference(resolution,[],[f122,f89])).
% 1.44/0.63  fof(f89,plain,(
% 1.44/0.63    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))) )),
% 1.44/0.63    inference(cnf_transformation,[],[f44])).
% 1.44/0.63  fof(f44,plain,(
% 1.44/0.63    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.44/0.63    inference(ennf_transformation,[],[f5])).
% 1.44/0.63  fof(f5,axiom,(
% 1.44/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 1.44/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 1.44/0.63  fof(f336,plain,(
% 1.44/0.63    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) | ~spl4_2),
% 1.44/0.63    inference(subsumption_resolution,[],[f335,f129])).
% 1.44/0.63  fof(f335,plain,(
% 1.44/0.63    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3) | ~spl4_2),
% 1.44/0.63    inference(subsumption_resolution,[],[f331,f60])).
% 1.44/0.63  fof(f331,plain,(
% 1.44/0.63    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_2),
% 1.44/0.63    inference(resolution,[],[f219,f72])).
% 1.44/0.63  fof(f72,plain,(
% 1.44/0.63    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.44/0.63    inference(cnf_transformation,[],[f30])).
% 1.44/0.63  fof(f136,plain,(
% 1.44/0.63    sK3 = k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3)),
% 1.44/0.63    inference(resolution,[],[f129,f103])).
% 1.44/0.63  fof(f882,plain,(
% 1.44/0.63    k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3) | (~spl4_3 | ~spl4_6)),
% 1.44/0.63    inference(forward_demodulation,[],[f878,f160])).
% 1.44/0.63  fof(f160,plain,(
% 1.44/0.63    k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)),
% 1.44/0.63    inference(subsumption_resolution,[],[f159,f57])).
% 1.44/0.63  fof(f159,plain,(
% 1.44/0.63    k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2) | ~v1_funct_1(sK2)),
% 1.44/0.63    inference(subsumption_resolution,[],[f158,f58])).
% 1.44/0.63  fof(f158,plain,(
% 1.44/0.63    k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.44/0.63    inference(subsumption_resolution,[],[f157,f59])).
% 1.44/0.63  fof(f157,plain,(
% 1.44/0.63    k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.44/0.63    inference(subsumption_resolution,[],[f156,f65])).
% 1.44/0.63  fof(f65,plain,(
% 1.44/0.63    v2_funct_1(sK2)),
% 1.44/0.63    inference(cnf_transformation,[],[f54])).
% 1.44/0.63  fof(f156,plain,(
% 1.44/0.63    ~v2_funct_1(sK2) | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.44/0.63    inference(subsumption_resolution,[],[f144,f67])).
% 1.44/0.63  fof(f67,plain,(
% 1.44/0.63    k1_xboole_0 != sK1),
% 1.44/0.63    inference(cnf_transformation,[],[f54])).
% 1.44/0.63  fof(f144,plain,(
% 1.44/0.63    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.44/0.63    inference(trivial_inequality_removal,[],[f143])).
% 1.44/0.63  fof(f143,plain,(
% 1.44/0.63    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.44/0.63    inference(superposition,[],[f70,f63])).
% 1.44/0.63  fof(f70,plain,(
% 1.44/0.63    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.44/0.63    inference(cnf_transformation,[],[f28])).
% 1.44/0.63  fof(f28,plain,(
% 1.44/0.63    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.44/0.63    inference(flattening,[],[f27])).
% 1.44/0.63  fof(f27,plain,(
% 1.44/0.63    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.44/0.63    inference(ennf_transformation,[],[f21])).
% 1.44/0.63  fof(f21,axiom,(
% 1.44/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 1.44/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 1.44/0.63  fof(f878,plain,(
% 1.44/0.63    k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),sK3) | (~spl4_3 | ~spl4_6)),
% 1.44/0.63    inference(resolution,[],[f564,f231])).
% 1.44/0.63  fof(f231,plain,(
% 1.44/0.63    v1_relat_1(k2_funct_1(sK2)) | ~spl4_3),
% 1.44/0.63    inference(avatar_component_clause,[],[f230])).
% 1.44/0.63  fof(f230,plain,(
% 1.44/0.63    spl4_3 <=> v1_relat_1(k2_funct_1(sK2))),
% 1.44/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.44/0.63  fof(f564,plain,(
% 1.44/0.63    ( ! [X13] : (~v1_relat_1(X13) | k5_relat_1(k5_relat_1(X13,sK2),sK3) = k5_relat_1(X13,k6_partfun1(sK0))) ) | ~spl4_6),
% 1.44/0.63    inference(forward_demodulation,[],[f551,f316])).
% 1.44/0.63  fof(f551,plain,(
% 1.44/0.63    ( ! [X13] : (~v1_relat_1(X13) | k5_relat_1(k5_relat_1(X13,sK2),sK3) = k5_relat_1(X13,k5_relat_1(sK2,sK3))) )),
% 1.44/0.63    inference(resolution,[],[f133,f129])).
% 1.44/0.63  fof(f133,plain,(
% 1.44/0.63    ( ! [X2,X3] : (~v1_relat_1(X2) | ~v1_relat_1(X3) | k5_relat_1(k5_relat_1(X3,sK2),X2) = k5_relat_1(X3,k5_relat_1(sK2,X2))) )),
% 1.44/0.63    inference(resolution,[],[f122,f89])).
% 1.44/0.63  fof(f737,plain,(
% 1.44/0.63    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_6 | ~spl4_7)),
% 1.44/0.63    inference(backward_demodulation,[],[f253,f708])).
% 1.44/0.63  fof(f708,plain,(
% 1.44/0.63    sK0 = k1_relat_1(sK2) | (~spl4_1 | ~spl4_2 | ~spl4_6 | ~spl4_7)),
% 1.44/0.63    inference(backward_demodulation,[],[f334,f706])).
% 1.44/0.63  fof(f253,plain,(
% 1.44/0.63    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(k1_relat_1(sK2))) | ~spl4_3),
% 1.44/0.63    inference(forward_demodulation,[],[f248,f203])).
% 1.44/0.63  fof(f203,plain,(
% 1.44/0.63    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.44/0.63    inference(subsumption_resolution,[],[f115,f122])).
% 1.44/0.63  fof(f115,plain,(
% 1.44/0.63    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.44/0.63    inference(subsumption_resolution,[],[f113,f57])).
% 1.44/0.63  fof(f113,plain,(
% 1.44/0.63    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.44/0.63    inference(resolution,[],[f65,f72])).
% 1.44/0.63  fof(f248,plain,(
% 1.44/0.63    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2)))) | ~spl4_3),
% 1.44/0.63    inference(resolution,[],[f231,f104])).
% 1.44/0.63  fof(f383,plain,(
% 1.44/0.63    spl4_7),
% 1.44/0.63    inference(avatar_contradiction_clause,[],[f382])).
% 1.44/0.63  fof(f382,plain,(
% 1.44/0.63    $false | spl4_7),
% 1.44/0.63    inference(subsumption_resolution,[],[f381,f129])).
% 1.44/0.63  fof(f381,plain,(
% 1.44/0.63    ~v1_relat_1(sK3) | spl4_7),
% 1.44/0.63    inference(subsumption_resolution,[],[f380,f60])).
% 1.44/0.63  fof(f380,plain,(
% 1.44/0.63    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl4_7),
% 1.44/0.63    inference(resolution,[],[f375,f73])).
% 1.44/0.63  fof(f73,plain,(
% 1.44/0.63    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.44/0.63    inference(cnf_transformation,[],[f32])).
% 1.44/0.63  fof(f32,plain,(
% 1.44/0.63    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.44/0.63    inference(flattening,[],[f31])).
% 1.44/0.63  fof(f31,plain,(
% 1.44/0.63    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.44/0.63    inference(ennf_transformation,[],[f9])).
% 1.44/0.63  fof(f9,axiom,(
% 1.44/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.44/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.44/0.63  fof(f375,plain,(
% 1.44/0.63    ~v1_relat_1(k2_funct_1(sK3)) | spl4_7),
% 1.44/0.63    inference(avatar_component_clause,[],[f373])).
% 1.44/0.63  fof(f324,plain,(
% 1.44/0.63    spl4_2 | ~spl4_6),
% 1.44/0.63    inference(avatar_contradiction_clause,[],[f323])).
% 1.44/0.63  fof(f323,plain,(
% 1.44/0.63    $false | (spl4_2 | ~spl4_6)),
% 1.44/0.63    inference(subsumption_resolution,[],[f322,f101])).
% 1.44/0.63  fof(f101,plain,(
% 1.44/0.63    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.44/0.63    inference(definition_unfolding,[],[f80,f84])).
% 1.44/0.63  fof(f80,plain,(
% 1.44/0.63    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.44/0.63    inference(cnf_transformation,[],[f10])).
% 1.44/0.63  fof(f10,axiom,(
% 1.44/0.63    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.44/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.44/0.63  fof(f322,plain,(
% 1.44/0.63    ~v2_funct_1(k6_partfun1(sK0)) | (spl4_2 | ~spl4_6)),
% 1.44/0.63    inference(forward_demodulation,[],[f321,f277])).
% 1.44/0.63  fof(f321,plain,(
% 1.44/0.63    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | spl4_2),
% 1.44/0.63    inference(subsumption_resolution,[],[f320,f60])).
% 1.44/0.63  fof(f320,plain,(
% 1.44/0.63    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | ~v1_funct_1(sK3) | spl4_2),
% 1.44/0.63    inference(subsumption_resolution,[],[f319,f66])).
% 1.44/0.63  fof(f66,plain,(
% 1.44/0.63    k1_xboole_0 != sK0),
% 1.44/0.63    inference(cnf_transformation,[],[f54])).
% 1.44/0.63  fof(f319,plain,(
% 1.44/0.63    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | k1_xboole_0 = sK0 | ~v1_funct_1(sK3) | spl4_2),
% 1.44/0.63    inference(subsumption_resolution,[],[f318,f62])).
% 1.44/0.63  fof(f318,plain,(
% 1.44/0.63    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_xboole_0 = sK0 | ~v1_funct_1(sK3) | spl4_2),
% 1.44/0.63    inference(subsumption_resolution,[],[f317,f220])).
% 1.44/0.63  fof(f220,plain,(
% 1.44/0.63    ~v2_funct_1(sK3) | spl4_2),
% 1.44/0.63    inference(avatar_component_clause,[],[f218])).
% 1.44/0.63  fof(f317,plain,(
% 1.44/0.63    v2_funct_1(sK3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_xboole_0 = sK0 | ~v1_funct_1(sK3)),
% 1.44/0.63    inference(resolution,[],[f150,f61])).
% 1.44/0.63  fof(f150,plain,(
% 1.44/0.63    ( ! [X2,X3] : (~v1_funct_2(X3,sK1,X2) | v2_funct_1(X3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | k1_xboole_0 = X2 | ~v1_funct_1(X3)) )),
% 1.44/0.63    inference(subsumption_resolution,[],[f149,f57])).
% 1.44/0.63  fof(f149,plain,(
% 1.44/0.63    ( ! [X2,X3] : (k1_xboole_0 = X2 | v2_funct_1(X3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | ~v1_funct_2(X3,sK1,X2) | ~v1_funct_1(X3) | ~v1_funct_1(sK2)) )),
% 1.44/0.63    inference(subsumption_resolution,[],[f148,f58])).
% 1.44/0.63  fof(f148,plain,(
% 1.44/0.63    ( ! [X2,X3] : (k1_xboole_0 = X2 | v2_funct_1(X3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | ~v1_funct_2(X3,sK1,X2) | ~v1_funct_1(X3) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) )),
% 1.44/0.63    inference(subsumption_resolution,[],[f146,f59])).
% 1.44/0.63  fof(f146,plain,(
% 1.44/0.63    ( ! [X2,X3] : (k1_xboole_0 = X2 | v2_funct_1(X3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | ~v1_funct_2(X3,sK1,X2) | ~v1_funct_1(X3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) )),
% 1.44/0.63    inference(trivial_inequality_removal,[],[f141])).
% 1.44/0.63  fof(f141,plain,(
% 1.44/0.63    ( ! [X2,X3] : (sK1 != sK1 | k1_xboole_0 = X2 | v2_funct_1(X3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | ~v1_funct_2(X3,sK1,X2) | ~v1_funct_1(X3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) )),
% 1.44/0.63    inference(superposition,[],[f77,f63])).
% 1.44/0.63  fof(f77,plain,(
% 1.44/0.63    ( ! [X4,X2,X0,X3,X1] : (k2_relset_1(X0,X1,X3) != X1 | k1_xboole_0 = X2 | v2_funct_1(X4) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.44/0.63    inference(cnf_transformation,[],[f34])).
% 1.44/0.63  fof(f34,plain,(
% 1.44/0.63    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.44/0.63    inference(flattening,[],[f33])).
% 1.44/0.63  fof(f33,plain,(
% 1.44/0.63    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.44/0.63    inference(ennf_transformation,[],[f20])).
% 1.44/0.63  fof(f20,axiom,(
% 1.44/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.44/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).
% 1.44/0.63  fof(f304,plain,(
% 1.44/0.63    spl4_5),
% 1.44/0.63    inference(avatar_contradiction_clause,[],[f303])).
% 1.44/0.63  fof(f303,plain,(
% 1.44/0.63    $false | spl4_5),
% 1.44/0.63    inference(subsumption_resolution,[],[f302,f57])).
% 1.44/0.63  fof(f302,plain,(
% 1.44/0.63    ~v1_funct_1(sK2) | spl4_5),
% 1.44/0.63    inference(subsumption_resolution,[],[f301,f59])).
% 1.44/0.63  fof(f301,plain,(
% 1.44/0.63    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl4_5),
% 1.44/0.63    inference(subsumption_resolution,[],[f300,f60])).
% 1.44/0.63  fof(f300,plain,(
% 1.44/0.63    ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl4_5),
% 1.44/0.63    inference(subsumption_resolution,[],[f299,f62])).
% 1.44/0.63  fof(f299,plain,(
% 1.44/0.63    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl4_5),
% 1.44/0.63    inference(resolution,[],[f273,f86])).
% 1.44/0.63  fof(f86,plain,(
% 1.44/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.44/0.63    inference(cnf_transformation,[],[f40])).
% 1.44/0.63  fof(f40,plain,(
% 1.44/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.44/0.63    inference(flattening,[],[f39])).
% 1.44/0.63  fof(f39,plain,(
% 1.44/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.44/0.63    inference(ennf_transformation,[],[f16])).
% 1.44/0.63  fof(f16,axiom,(
% 1.44/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.44/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.44/0.63  fof(f273,plain,(
% 1.44/0.63    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_5),
% 1.44/0.63    inference(avatar_component_clause,[],[f271])).
% 1.44/0.63  fof(f271,plain,(
% 1.44/0.63    spl4_5 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.44/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.44/0.63  fof(f278,plain,(
% 1.44/0.63    ~spl4_5 | spl4_6),
% 1.44/0.63    inference(avatar_split_clause,[],[f163,f275,f271])).
% 1.44/0.63  fof(f163,plain,(
% 1.44/0.63    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.44/0.63    inference(subsumption_resolution,[],[f161,f107])).
% 1.44/0.63  fof(f107,plain,(
% 1.44/0.63    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.44/0.63    inference(definition_unfolding,[],[f95,f84])).
% 1.44/0.63  fof(f95,plain,(
% 1.44/0.63    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.44/0.63    inference(cnf_transformation,[],[f15])).
% 1.44/0.63  fof(f15,axiom,(
% 1.44/0.63    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.44/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 1.44/0.63  fof(f161,plain,(
% 1.44/0.63    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.44/0.63    inference(resolution,[],[f64,f81])).
% 1.44/0.63  fof(f81,plain,(
% 1.44/0.63    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.44/0.63    inference(cnf_transformation,[],[f55])).
% 1.44/0.63  fof(f55,plain,(
% 1.44/0.63    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.63    inference(nnf_transformation,[],[f36])).
% 1.44/0.63  fof(f36,plain,(
% 1.44/0.63    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.63    inference(flattening,[],[f35])).
% 1.44/0.63  fof(f35,plain,(
% 1.44/0.63    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.44/0.63    inference(ennf_transformation,[],[f14])).
% 1.44/0.63  fof(f14,axiom,(
% 1.44/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.44/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.44/0.63  fof(f247,plain,(
% 1.44/0.63    spl4_3),
% 1.44/0.63    inference(avatar_contradiction_clause,[],[f246])).
% 1.44/0.63  fof(f246,plain,(
% 1.44/0.63    $false | spl4_3),
% 1.44/0.63    inference(subsumption_resolution,[],[f245,f122])).
% 1.44/0.63  fof(f245,plain,(
% 1.44/0.63    ~v1_relat_1(sK2) | spl4_3),
% 1.44/0.63    inference(subsumption_resolution,[],[f244,f57])).
% 1.44/0.63  fof(f244,plain,(
% 1.44/0.63    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_3),
% 1.44/0.63    inference(resolution,[],[f232,f73])).
% 1.44/0.63  fof(f232,plain,(
% 1.44/0.63    ~v1_relat_1(k2_funct_1(sK2)) | spl4_3),
% 1.44/0.63    inference(avatar_component_clause,[],[f230])).
% 1.44/0.63  fof(f221,plain,(
% 1.44/0.63    spl4_1 | ~spl4_2),
% 1.44/0.63    inference(avatar_split_clause,[],[f187,f218,f214])).
% 1.44/0.63  fof(f187,plain,(
% 1.44/0.63    ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 1.44/0.63    inference(subsumption_resolution,[],[f186,f60])).
% 1.44/0.63  fof(f186,plain,(
% 1.44/0.63    ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_1(sK3)),
% 1.44/0.63    inference(subsumption_resolution,[],[f185,f61])).
% 1.44/0.63  fof(f185,plain,(
% 1.44/0.63    ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.44/0.63    inference(subsumption_resolution,[],[f184,f62])).
% 1.44/0.63  fof(f184,plain,(
% 1.44/0.63    ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.44/0.63    inference(subsumption_resolution,[],[f175,f66])).
% 1.44/0.63  fof(f175,plain,(
% 1.44/0.63    k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.44/0.63    inference(trivial_inequality_removal,[],[f172])).
% 1.44/0.63  fof(f172,plain,(
% 1.44/0.63    sK0 != sK0 | k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.44/0.63    inference(superposition,[],[f69,f169])).
% 1.44/0.63  fof(f69,plain,(
% 1.44/0.63    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.44/0.63    inference(cnf_transformation,[],[f28])).
% 1.44/0.63  % SZS output end Proof for theBenchmark
% 1.44/0.63  % (32217)------------------------------
% 1.44/0.63  % (32217)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.63  % (32217)Termination reason: Refutation
% 1.44/0.63  
% 1.44/0.63  % (32217)Memory used [KB]: 11257
% 1.44/0.63  % (32217)Time elapsed: 0.199 s
% 1.44/0.63  % (32217)------------------------------
% 1.44/0.63  % (32217)------------------------------
% 1.44/0.63  % (32192)Success in time 0.273 s
%------------------------------------------------------------------------------
