%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1343+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:19 EST 2020

% Result     : Theorem 8.56s
% Output     : Refutation 8.56s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 190 expanded)
%              Number of leaves         :   13 (  79 expanded)
%              Depth                    :   16
%              Number of atoms          :  241 (1563 expanded)
%              Number of equality atoms :   71 ( 410 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11345,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f9501,f11341])).

fof(f11341,plain,(
    ~ spl192_90 ),
    inference(avatar_contradiction_clause,[],[f11340])).

fof(f11340,plain,
    ( $false
    | ~ spl192_90 ),
    inference(subsumption_resolution,[],[f11339,f7812])).

fof(f7812,plain,(
    ! [X44] : k9_relat_1(sK5,X44) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X44) ),
    inference(resolution,[],[f3605,f3654])).

fof(f3654,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2499])).

fof(f2499,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1233])).

fof(f1233,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f3605,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f3162])).

fof(f3162,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6) != k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK6)
    & v2_funct_1(sK5)
    & k2_struct_0(sK4) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    & v1_funct_1(sK5)
    & l1_struct_0(sK4)
    & l1_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f2453,f3161,f3160,f3159,f3158])).

fof(f3158,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                    & v2_funct_1(X2)
                    & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(X1),X2),X3)
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f3159,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(X1),X2),X3)
                & v2_funct_1(X2)
                & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X2)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X2,X3) != k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X2),X3)
              & v2_funct_1(X2)
              & k2_struct_0(sK4) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X2)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
          & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(sK4))
          & v1_funct_1(X2) )
      & l1_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f3160,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X2,X3) != k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X2),X3)
            & v2_funct_1(X2)
            & k2_struct_0(sK4) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X2)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
        & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(sK4))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X3) != k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),X3)
          & v2_funct_1(sK5)
          & k2_struct_0(sK4) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
      & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f3161,plain,
    ( ? [X3] :
        ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X3) != k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),X3)
        & v2_funct_1(sK5)
        & k2_struct_0(sK4) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) )
   => ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6) != k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK6)
      & v2_funct_1(sK5)
      & k2_struct_0(sK4) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
      & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f2453,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f2452])).

fof(f2452,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2415])).

fof(f2415,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( ( v2_funct_1(X2)
                        & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                     => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f2414])).

fof(f2414,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( v2_funct_1(X2)
                      & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                   => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tops_2)).

fof(f11339,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6) != k9_relat_1(sK5,sK6)
    | ~ spl192_90 ),
    inference(forward_demodulation,[],[f11338,f5651])).

fof(f5651,plain,
    ( ! [X320] : k9_relat_1(sK5,X320) = k10_relat_1(k2_funct_1(sK5),X320)
    | ~ spl192_90 ),
    inference(avatar_component_clause,[],[f5650])).

fof(f5650,plain,
    ( spl192_90
  <=> ! [X320] : k9_relat_1(sK5,X320) = k10_relat_1(k2_funct_1(sK5),X320) ),
    introduced(avatar_definition,[new_symbols(naming,[spl192_90])])).

fof(f11338,plain,(
    k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6) != k10_relat_1(k2_funct_1(sK5),sK6) ),
    inference(forward_demodulation,[],[f11332,f7722])).

fof(f7722,plain,(
    k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_funct_1(sK5) ),
    inference(subsumption_resolution,[],[f7721,f4829])).

fof(f4829,plain,(
    u1_struct_0(sK4) = k2_struct_0(sK4) ),
    inference(resolution,[],[f3602,f3741])).

fof(f3741,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2557])).

fof(f2557,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1773])).

fof(f1773,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f3602,plain,(
    l1_struct_0(sK4) ),
    inference(cnf_transformation,[],[f3162])).

fof(f7721,plain,
    ( u1_struct_0(sK4) != k2_struct_0(sK4)
    | k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_funct_1(sK5) ),
    inference(forward_demodulation,[],[f7015,f3607])).

fof(f3607,plain,(
    k2_struct_0(sK4) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) ),
    inference(cnf_transformation,[],[f3162])).

fof(f7015,plain,
    ( k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_funct_1(sK5)
    | u1_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) ),
    inference(subsumption_resolution,[],[f7014,f3603])).

fof(f3603,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f3162])).

fof(f7014,plain,
    ( k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_funct_1(sK5)
    | u1_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
    | ~ v1_funct_1(sK5) ),
    inference(subsumption_resolution,[],[f7013,f3605])).

fof(f7013,plain,
    ( k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_funct_1(sK5)
    | u1_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_1(sK5) ),
    inference(subsumption_resolution,[],[f6816,f3608])).

fof(f3608,plain,(
    v2_funct_1(sK5) ),
    inference(cnf_transformation,[],[f3162])).

fof(f6816,plain,
    ( k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_funct_1(sK5)
    | ~ v2_funct_1(sK5)
    | u1_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_1(sK5) ),
    inference(resolution,[],[f3604,f3630])).

fof(f3630,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f2472])).

fof(f2472,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f2471])).

fof(f2471,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2245])).

fof(f2245,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f3604,plain,(
    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f3162])).

fof(f11332,plain,(
    k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6) != k10_relat_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK6) ),
    inference(subsumption_resolution,[],[f11331,f7034])).

fof(f7034,plain,(
    m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(subsumption_resolution,[],[f7033,f3603])).

fof(f7033,plain,
    ( m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK5) ),
    inference(subsumption_resolution,[],[f6819,f3605])).

fof(f6819,plain,
    ( m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_1(sK5) ),
    inference(resolution,[],[f3604,f3633])).

fof(f3633,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f2474])).

fof(f2474,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f2473])).

fof(f2473,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2252])).

fof(f2252,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(f11331,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6) != k10_relat_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK6)
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(superposition,[],[f3609,f3614])).

fof(f3614,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2458])).

fof(f2458,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1234])).

fof(f1234,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f3609,plain,(
    k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6) != k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK6) ),
    inference(cnf_transformation,[],[f3162])).

fof(f9501,plain,(
    spl192_90 ),
    inference(avatar_split_clause,[],[f9500,f5650])).

fof(f9500,plain,(
    ! [X76] : k9_relat_1(sK5,X76) = k10_relat_1(k2_funct_1(sK5),X76) ),
    inference(global_subsumption,[],[f7850,f9499])).

fof(f9499,plain,(
    ! [X76] :
      ( k9_relat_1(sK5,X76) = k10_relat_1(k2_funct_1(sK5),X76)
      | ~ v1_relat_1(sK5) ) ),
    inference(subsumption_resolution,[],[f6464,f3603])).

fof(f6464,plain,(
    ! [X76] :
      ( k9_relat_1(sK5,X76) = k10_relat_1(k2_funct_1(sK5),X76)
      | ~ v1_funct_1(sK5)
      | ~ v1_relat_1(sK5) ) ),
    inference(resolution,[],[f3608,f4191])).

fof(f4191,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2817])).

fof(f2817,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f2816])).

fof(f2816,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f974])).

fof(f974,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).

fof(f7850,plain,(
    v1_relat_1(sK5) ),
    inference(resolution,[],[f3605,f3747])).

fof(f3747,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2565])).

fof(f2565,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1210])).

fof(f1210,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
%------------------------------------------------------------------------------
