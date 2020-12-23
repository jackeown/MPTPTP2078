%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1344+2 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 10.10s
% Output     : Refutation 10.10s
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
fof(f12823,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f9665,f12822])).

fof(f12822,plain,(
    ~ spl192_87 ),
    inference(avatar_contradiction_clause,[],[f12821])).

fof(f12821,plain,
    ( $false
    | ~ spl192_87 ),
    inference(subsumption_resolution,[],[f12820,f8288])).

fof(f8288,plain,(
    ! [X47] : k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X47) = k10_relat_1(sK5,X47) ),
    inference(resolution,[],[f3608,f3659])).

fof(f3659,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2502])).

fof(f2502,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1234])).

fof(f1234,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f3608,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f3165])).

fof(f3165,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6) != k7_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK6)
    & v2_funct_1(sK5)
    & k2_struct_0(sK4) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    & v1_funct_1(sK5)
    & l1_struct_0(sK4)
    & l1_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f2454,f3164,f3163,f3162,f3161])).

fof(f3161,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                    & v2_funct_1(X2)
                    & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X2,X3) != k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(X1),X2),X3)
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f3162,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X2,X3) != k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(X1),X2),X3)
                & v2_funct_1(X2)
                & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X2)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X2,X3) != k7_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X2),X3)
              & v2_funct_1(X2)
              & k2_struct_0(sK4) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X2)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
          & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(sK4))
          & v1_funct_1(X2) )
      & l1_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f3163,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X2,X3) != k7_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),X2),X3)
            & v2_funct_1(X2)
            & k2_struct_0(sK4) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),X2)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
        & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(sK4))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X3) != k7_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),X3)
          & v2_funct_1(sK5)
          & k2_struct_0(sK4) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
      & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f3164,plain,
    ( ? [X3] :
        ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X3) != k7_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),X3)
        & v2_funct_1(sK5)
        & k2_struct_0(sK4) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
   => ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6) != k7_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK6)
      & v2_funct_1(sK5)
      & k2_struct_0(sK4) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
      & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) ) ),
    introduced(choice_axiom,[])).

fof(f2454,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f2453])).

fof(f2453,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2416])).

fof(f2416,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v2_funct_1(X2)
                        & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                     => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f2415])).

fof(f2415,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v2_funct_1(X2)
                      & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                   => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_tops_2)).

fof(f12820,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6) != k10_relat_1(sK5,sK6)
    | ~ spl192_87 ),
    inference(forward_demodulation,[],[f12819,f5659])).

fof(f5659,plain,
    ( ! [X485] : k10_relat_1(sK5,X485) = k9_relat_1(k2_funct_1(sK5),X485)
    | ~ spl192_87 ),
    inference(avatar_component_clause,[],[f5658])).

fof(f5658,plain,
    ( spl192_87
  <=> ! [X485] : k10_relat_1(sK5,X485) = k9_relat_1(k2_funct_1(sK5),X485) ),
    introduced(avatar_definition,[new_symbols(naming,[spl192_87])])).

fof(f12819,plain,(
    k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6) != k9_relat_1(k2_funct_1(sK5),sK6) ),
    inference(forward_demodulation,[],[f12818,f7991])).

fof(f7991,plain,(
    k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_funct_1(sK5) ),
    inference(subsumption_resolution,[],[f7990,f4845])).

fof(f4845,plain,(
    u1_struct_0(sK4) = k2_struct_0(sK4) ),
    inference(resolution,[],[f3605,f3745])).

fof(f3745,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2560])).

fof(f2560,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1773])).

fof(f1773,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f3605,plain,(
    l1_struct_0(sK4) ),
    inference(cnf_transformation,[],[f3165])).

fof(f7990,plain,
    ( u1_struct_0(sK4) != k2_struct_0(sK4)
    | k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_funct_1(sK5) ),
    inference(forward_demodulation,[],[f7252,f3610])).

fof(f3610,plain,(
    k2_struct_0(sK4) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) ),
    inference(cnf_transformation,[],[f3165])).

fof(f7252,plain,
    ( k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_funct_1(sK5)
    | u1_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) ),
    inference(subsumption_resolution,[],[f7251,f3606])).

fof(f3606,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f3165])).

fof(f7251,plain,
    ( k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_funct_1(sK5)
    | u1_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
    | ~ v1_funct_1(sK5) ),
    inference(subsumption_resolution,[],[f7250,f3608])).

fof(f7250,plain,
    ( k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_funct_1(sK5)
    | u1_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_1(sK5) ),
    inference(subsumption_resolution,[],[f7072,f3611])).

fof(f3611,plain,(
    v2_funct_1(sK5) ),
    inference(cnf_transformation,[],[f3165])).

fof(f7072,plain,
    ( k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_funct_1(sK5)
    | ~ v2_funct_1(sK5)
    | u1_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_1(sK5) ),
    inference(resolution,[],[f3607,f3643])).

fof(f3643,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f2483])).

fof(f2483,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f2482])).

fof(f2482,plain,(
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

fof(f3607,plain,(
    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f3165])).

fof(f12818,plain,(
    k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6) != k9_relat_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK6) ),
    inference(subsumption_resolution,[],[f12817,f7271])).

fof(f7271,plain,(
    m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(subsumption_resolution,[],[f7270,f3606])).

fof(f7270,plain,
    ( m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK5) ),
    inference(subsumption_resolution,[],[f7075,f3608])).

fof(f7075,plain,
    ( m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_1(sK5) ),
    inference(resolution,[],[f3607,f3646])).

fof(f3646,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f2485])).

fof(f2485,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f2484])).

fof(f2484,plain,(
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

fof(f12817,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6) != k9_relat_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK6)
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(superposition,[],[f3612,f3626])).

fof(f3626,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2469])).

fof(f2469,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1233])).

fof(f1233,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f3612,plain,(
    k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6) != k7_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK6) ),
    inference(cnf_transformation,[],[f3165])).

fof(f9665,plain,(
    spl192_87 ),
    inference(avatar_split_clause,[],[f9664,f5658])).

fof(f9664,plain,(
    ! [X91] : k10_relat_1(sK5,X91) = k9_relat_1(k2_funct_1(sK5),X91) ),
    inference(global_subsumption,[],[f8323,f9663])).

fof(f9663,plain,(
    ! [X91] :
      ( k10_relat_1(sK5,X91) = k9_relat_1(k2_funct_1(sK5),X91)
      | ~ v1_relat_1(sK5) ) ),
    inference(subsumption_resolution,[],[f6485,f3606])).

fof(f6485,plain,(
    ! [X91] :
      ( k10_relat_1(sK5,X91) = k9_relat_1(k2_funct_1(sK5),X91)
      | ~ v1_funct_1(sK5)
      | ~ v1_relat_1(sK5) ) ),
    inference(resolution,[],[f3611,f4235])).

fof(f4235,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2814])).

fof(f2814,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f2813])).

fof(f2813,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f975])).

fof(f975,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

fof(f8323,plain,(
    v1_relat_1(sK5) ),
    inference(resolution,[],[f3608,f3751])).

fof(f3751,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2568])).

fof(f2568,plain,(
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
