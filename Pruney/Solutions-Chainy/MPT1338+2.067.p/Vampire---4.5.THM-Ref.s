%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:10 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  208 (3244 expanded)
%              Number of leaves         :   32 (1127 expanded)
%              Depth                    :   25
%              Number of atoms          :  748 (24878 expanded)
%              Number of equality atoms :  150 (7876 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f592,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f122,f134,f151,f157,f163,f185,f188,f221,f316,f352,f547,f579,f591])).

fof(f591,plain,
    ( ~ spl3_4
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_16
    | spl3_20 ),
    inference(avatar_contradiction_clause,[],[f590])).

fof(f590,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_16
    | spl3_20 ),
    inference(subsumption_resolution,[],[f589,f365])).

fof(f365,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | spl3_20 ),
    inference(avatar_component_clause,[],[f364])).

fof(f364,plain,
    ( spl3_20
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f589,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f585,f77])).

fof(f77,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f585,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(k6_relat_1(k2_relat_1(sK2)))
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_16 ),
    inference(superposition,[],[f77,f548])).

fof(f548,plain,
    ( k6_relat_1(k2_relat_1(sK2)) = k6_relat_1(k1_relat_1(k2_funct_1(sK2)))
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f328,f156])).

fof(f156,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl3_7
  <=> k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f328,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k1_relat_1(k2_funct_1(sK2)))
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f327,f162])).

fof(f162,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl3_8
  <=> sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f327,plain,
    ( k5_relat_1(k2_funct_1(sK2),k2_funct_1(k2_funct_1(sK2))) = k6_relat_1(k1_relat_1(k2_funct_1(sK2)))
    | ~ spl3_4
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f326,f133])).

fof(f133,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl3_4
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f326,plain,
    ( k5_relat_1(k2_funct_1(sK2),k2_funct_1(k2_funct_1(sK2))) = k6_relat_1(k1_relat_1(k2_funct_1(sK2)))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f318,f209])).

fof(f209,plain,(
    v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f208,f70])).

fof(f70,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,
    ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
      | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) )
    & v2_funct_1(sK2)
    & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f61,f60,f59])).

fof(f59,plain,
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
              ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))
              | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) )
            & v2_funct_1(X2)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))
            | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) )
          & v2_funct_1(X2)
          & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_struct_0(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ? [X2] :
        ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))
          | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) )
        & v2_funct_1(X2)
        & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
        | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) )
      & v2_funct_1(sK2)
      & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
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
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).

fof(f208,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f207,f165])).

fof(f165,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f164,f124])).

fof(f124,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f69,f78])).

fof(f78,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f69,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f62])).

fof(f164,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f71,f123])).

fof(f123,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(resolution,[],[f67,f78])).

fof(f67,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f62])).

fof(f71,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f62])).

fof(f207,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f206,f167])).

fof(f167,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f166,f123])).

fof(f166,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f72,f124])).

fof(f72,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f62])).

fof(f206,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f200,f74])).

fof(f74,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f200,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(trivial_inequality_removal,[],[f195])).

fof(f195,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f105,f191])).

fof(f191,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(forward_demodulation,[],[f190,f123])).

fof(f190,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(forward_demodulation,[],[f73,f124])).

fof(f73,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | v1_funct_1(k2_funct_1(X2))
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f54])).

% (20565)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f318,plain,
    ( k5_relat_1(k2_funct_1(sK2),k2_funct_1(k2_funct_1(sK2))) = k6_relat_1(k1_relat_1(k2_funct_1(sK2)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_16 ),
    inference(resolution,[],[f305,f88])).

fof(f88,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f305,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f304])).

fof(f304,plain,
    ( spl3_16
  <=> v2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f579,plain,
    ( spl3_1
    | ~ spl3_3
    | ~ spl3_10
    | ~ spl3_20 ),
    inference(avatar_contradiction_clause,[],[f578])).

fof(f578,plain,
    ( $false
    | spl3_1
    | ~ spl3_3
    | ~ spl3_10
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f577,f455])).

fof(f455,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | spl3_1
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f403,f433])).

fof(f433,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f274,f372])).

fof(f372,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f238,f256])).

fof(f256,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2)
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(resolution,[],[f235,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

% (20561)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
fof(f235,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f167,f228])).

fof(f228,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f227,f128])).

fof(f128,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f227,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f226,f169])).

fof(f169,plain,(
    v4_relat_1(sK2,k2_struct_0(sK0)) ),
    inference(resolution,[],[f167,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f226,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ v1_relat_1(sK2)
    | ~ spl3_10 ),
    inference(resolution,[],[f184,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f184,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl3_10
  <=> v1_partfun1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f238,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2)
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f191,f228])).

fof(f274,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f273,f70])).

fof(f273,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f272,f234])).

fof(f234,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1))
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f165,f228])).

fof(f272,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f271,f235])).

fof(f271,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f270,f74])).

fof(f270,plain,
    ( ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(trivial_inequality_removal,[],[f263])).

fof(f263,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(superposition,[],[f108,f238])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f403,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | spl3_1
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f239,f372])).

fof(f239,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2))
    | spl3_1
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f225,f228])).

fof(f225,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | spl3_1 ),
    inference(forward_demodulation,[],[f224,f123])).

fof(f224,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | spl3_1 ),
    inference(forward_demodulation,[],[f117,f124])).

fof(f117,plain,
    ( k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl3_1
  <=> k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f577,plain,
    ( k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_10
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f459,f366])).

fof(f366,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f364])).

fof(f459,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(resolution,[],[f434,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f434,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f282,f372])).

fof(f282,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2))))
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f281,f70])).

fof(f281,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2))))
    | ~ v1_funct_1(sK2)
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f280,f234])).

fof(f280,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f279,f235])).

fof(f279,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f267,f74])).

fof(f267,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(trivial_inequality_removal,[],[f266])).

fof(f266,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(superposition,[],[f107,f238])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f547,plain,
    ( spl3_2
    | ~ spl3_3
    | ~ spl3_10
    | ~ spl3_17 ),
    inference(avatar_contradiction_clause,[],[f546])).

fof(f546,plain,
    ( $false
    | spl3_2
    | ~ spl3_3
    | ~ spl3_10
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f545,f228])).

fof(f545,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | spl3_2
    | ~ spl3_3
    | ~ spl3_10
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f544,f464])).

fof(f464,plain,
    ( k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_10
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f458,f309])).

fof(f309,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f308])).

fof(f308,plain,
    ( spl3_17
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f458,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(resolution,[],[f434,f103])).

fof(f544,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | spl3_2
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f543,f433])).

fof(f543,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | spl3_2
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f542,f233])).

fof(f233,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f123,f228])).

fof(f542,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2))
    | spl3_2
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f121,f399])).

fof(f399,plain,
    ( u1_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f124,f372])).

fof(f121,plain,
    ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl3_2
  <=> k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f352,plain,
    ( ~ spl3_4
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_16
    | spl3_17 ),
    inference(avatar_contradiction_clause,[],[f351])).

fof(f351,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_16
    | spl3_17 ),
    inference(subsumption_resolution,[],[f350,f310])).

fof(f310,plain,
    ( k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | spl3_17 ),
    inference(avatar_component_clause,[],[f308])).

fof(f350,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f346,f77])).

fof(f346,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k2_relat_1(k6_relat_1(k1_relat_1(sK2)))
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_16 ),
    inference(superposition,[],[f77,f332])).

fof(f332,plain,
    ( k6_relat_1(k1_relat_1(sK2)) = k6_relat_1(k2_relat_1(k2_funct_1(sK2)))
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f331,f150])).

fof(f150,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl3_6
  <=> k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f331,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k2_relat_1(k2_funct_1(sK2)))
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f330,f162])).

fof(f330,plain,
    ( k5_relat_1(k2_funct_1(k2_funct_1(sK2)),k2_funct_1(sK2)) = k6_relat_1(k2_relat_1(k2_funct_1(sK2)))
    | ~ spl3_4
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f329,f133])).

fof(f329,plain,
    ( k5_relat_1(k2_funct_1(k2_funct_1(sK2)),k2_funct_1(sK2)) = k6_relat_1(k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f319,f209])).

fof(f319,plain,
    ( k5_relat_1(k2_funct_1(k2_funct_1(sK2)),k2_funct_1(sK2)) = k6_relat_1(k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_16 ),
    inference(resolution,[],[f305,f89])).

fof(f89,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f316,plain,
    ( ~ spl3_3
    | spl3_16 ),
    inference(avatar_contradiction_clause,[],[f315])).

fof(f315,plain,
    ( $false
    | ~ spl3_3
    | spl3_16 ),
    inference(subsumption_resolution,[],[f314,f128])).

fof(f314,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_16 ),
    inference(subsumption_resolution,[],[f313,f70])).

fof(f313,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_16 ),
    inference(subsumption_resolution,[],[f312,f74])).

fof(f312,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_16 ),
    inference(resolution,[],[f306,f84])).

fof(f84,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f306,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | spl3_16 ),
    inference(avatar_component_clause,[],[f304])).

fof(f221,plain,(
    ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f220])).

fof(f220,plain,
    ( $false
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f219,f68])).

fof(f68,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f62])).

fof(f219,plain,
    ( v2_struct_0(sK1)
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f218,f69])).

fof(f218,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl3_9 ),
    inference(resolution,[],[f180,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f180,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl3_9
  <=> v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f188,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f187])).

fof(f187,plain,
    ( $false
    | spl3_3 ),
    inference(subsumption_resolution,[],[f186,f91])).

fof(f91,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f186,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))
    | spl3_3 ),
    inference(subsumption_resolution,[],[f174,f129])).

fof(f129,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f127])).

fof(f174,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) ),
    inference(resolution,[],[f167,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f185,plain,
    ( spl3_9
    | spl3_10 ),
    inference(avatar_split_clause,[],[f176,f182,f178])).

fof(f176,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0))
    | v1_xboole_0(k2_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f175,f70])).

fof(f175,plain,
    ( ~ v1_funct_1(sK2)
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | v1_xboole_0(k2_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f172,f165])).

fof(f172,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | v1_xboole_0(k2_struct_0(sK1)) ),
    inference(resolution,[],[f167,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_partfun1(X2,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f163,plain,
    ( ~ spl3_3
    | spl3_8 ),
    inference(avatar_split_clause,[],[f158,f160,f127])).

fof(f158,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f138,f70])).

fof(f138,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f74,f87])).

fof(f87,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

fof(f157,plain,
    ( ~ spl3_3
    | spl3_7 ),
    inference(avatar_split_clause,[],[f152,f154,f127])).

fof(f152,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f137,f70])).

fof(f137,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f74,f89])).

fof(f151,plain,
    ( ~ spl3_3
    | spl3_6 ),
    inference(avatar_split_clause,[],[f146,f148,f127])).

fof(f146,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f136,f70])).

fof(f136,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f74,f88])).

fof(f134,plain,
    ( ~ spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f125,f131,f127])).

fof(f125,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f70,f85])).

fof(f85,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f122,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f75,f119,f115])).

fof(f75,plain,
    ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f62])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:49:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (20552)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.50  % (20559)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.50  % (20552)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % (20553)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (20573)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f592,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f122,f134,f151,f157,f163,f185,f188,f221,f316,f352,f547,f579,f591])).
% 0.22/0.51  fof(f591,plain,(
% 0.22/0.51    ~spl3_4 | ~spl3_7 | ~spl3_8 | ~spl3_16 | spl3_20),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f590])).
% 0.22/0.51  fof(f590,plain,(
% 0.22/0.51    $false | (~spl3_4 | ~spl3_7 | ~spl3_8 | ~spl3_16 | spl3_20)),
% 0.22/0.51    inference(subsumption_resolution,[],[f589,f365])).
% 0.22/0.51  fof(f365,plain,(
% 0.22/0.51    k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | spl3_20),
% 0.22/0.51    inference(avatar_component_clause,[],[f364])).
% 0.22/0.51  fof(f364,plain,(
% 0.22/0.51    spl3_20 <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.51  fof(f589,plain,(
% 0.22/0.51    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl3_4 | ~spl3_7 | ~spl3_8 | ~spl3_16)),
% 0.22/0.51    inference(forward_demodulation,[],[f585,f77])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.51  fof(f585,plain,(
% 0.22/0.51    k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(k6_relat_1(k2_relat_1(sK2))) | (~spl3_4 | ~spl3_7 | ~spl3_8 | ~spl3_16)),
% 0.22/0.51    inference(superposition,[],[f77,f548])).
% 0.22/0.51  fof(f548,plain,(
% 0.22/0.51    k6_relat_1(k2_relat_1(sK2)) = k6_relat_1(k1_relat_1(k2_funct_1(sK2))) | (~spl3_4 | ~spl3_7 | ~spl3_8 | ~spl3_16)),
% 0.22/0.51    inference(forward_demodulation,[],[f328,f156])).
% 0.22/0.51  fof(f156,plain,(
% 0.22/0.51    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) | ~spl3_7),
% 0.22/0.51    inference(avatar_component_clause,[],[f154])).
% 0.22/0.51  fof(f154,plain,(
% 0.22/0.51    spl3_7 <=> k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.51  fof(f328,plain,(
% 0.22/0.51    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k1_relat_1(k2_funct_1(sK2))) | (~spl3_4 | ~spl3_8 | ~spl3_16)),
% 0.22/0.51    inference(forward_demodulation,[],[f327,f162])).
% 0.22/0.51  fof(f162,plain,(
% 0.22/0.51    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~spl3_8),
% 0.22/0.51    inference(avatar_component_clause,[],[f160])).
% 0.22/0.51  fof(f160,plain,(
% 0.22/0.51    spl3_8 <=> sK2 = k2_funct_1(k2_funct_1(sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.51  fof(f327,plain,(
% 0.22/0.51    k5_relat_1(k2_funct_1(sK2),k2_funct_1(k2_funct_1(sK2))) = k6_relat_1(k1_relat_1(k2_funct_1(sK2))) | (~spl3_4 | ~spl3_16)),
% 0.22/0.51    inference(subsumption_resolution,[],[f326,f133])).
% 0.22/0.51  fof(f133,plain,(
% 0.22/0.51    v1_relat_1(k2_funct_1(sK2)) | ~spl3_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f131])).
% 0.22/0.51  fof(f131,plain,(
% 0.22/0.51    spl3_4 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.51  fof(f326,plain,(
% 0.22/0.51    k5_relat_1(k2_funct_1(sK2),k2_funct_1(k2_funct_1(sK2))) = k6_relat_1(k1_relat_1(k2_funct_1(sK2))) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl3_16),
% 0.22/0.51    inference(subsumption_resolution,[],[f318,f209])).
% 0.22/0.51  fof(f209,plain,(
% 0.22/0.51    v1_funct_1(k2_funct_1(sK2))),
% 0.22/0.51    inference(subsumption_resolution,[],[f208,f70])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    v1_funct_1(sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f62])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    (((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f61,f60,f59])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    ? [X1] : (? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))) & v2_funct_1(X2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    ? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))) & v2_funct_1(X2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f25])).
% 0.22/0.51  fof(f25,negated_conjecture,(
% 0.22/0.51    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.22/0.51    inference(negated_conjecture,[],[f24])).
% 0.22/0.51  fof(f24,conjecture,(
% 0.22/0.51    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).
% 0.22/0.51  fof(f208,plain,(
% 0.22/0.51    v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f207,f165])).
% 0.22/0.51  fof(f165,plain,(
% 0.22/0.51    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.22/0.51    inference(forward_demodulation,[],[f164,f124])).
% 0.22/0.51  fof(f124,plain,(
% 0.22/0.51    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.22/0.51    inference(resolution,[],[f69,f78])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,axiom,(
% 0.22/0.51    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    l1_struct_0(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f62])).
% 0.22/0.51  fof(f164,plain,(
% 0.22/0.51    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.51    inference(backward_demodulation,[],[f71,f123])).
% 0.22/0.51  fof(f123,plain,(
% 0.22/0.51    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.22/0.51    inference(resolution,[],[f67,f78])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    l1_struct_0(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f62])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f62])).
% 0.22/0.51  fof(f207,plain,(
% 0.22/0.51    v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f206,f167])).
% 0.22/0.51  fof(f167,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.22/0.51    inference(forward_demodulation,[],[f166,f123])).
% 0.22/0.51  fof(f166,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))),
% 0.22/0.51    inference(forward_demodulation,[],[f72,f124])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.51    inference(cnf_transformation,[],[f62])).
% 0.22/0.51  fof(f206,plain,(
% 0.22/0.51    v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f200,f74])).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    v2_funct_1(sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f62])).
% 0.22/0.51  fof(f200,plain,(
% 0.22/0.51    v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f195])).
% 0.22/0.51  fof(f195,plain,(
% 0.22/0.51    k2_struct_0(sK1) != k2_struct_0(sK1) | v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 0.22/0.51    inference(superposition,[],[f105,f191])).
% 0.22/0.51  fof(f191,plain,(
% 0.22/0.51    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.51    inference(forward_demodulation,[],[f190,f123])).
% 0.22/0.51  fof(f190,plain,(
% 0.22/0.51    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.51    inference(forward_demodulation,[],[f73,f124])).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f62])).
% 0.22/0.51  fof(f105,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | v1_funct_1(k2_funct_1(X2)) | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f54])).
% 0.22/0.51  % (20565)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.51    inference(flattening,[],[f53])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.51    inference(ennf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.22/0.51  fof(f318,plain,(
% 0.22/0.51    k5_relat_1(k2_funct_1(sK2),k2_funct_1(k2_funct_1(sK2))) = k6_relat_1(k1_relat_1(k2_funct_1(sK2))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl3_16),
% 0.22/0.51    inference(resolution,[],[f305,f88])).
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,axiom,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 0.22/0.51  fof(f305,plain,(
% 0.22/0.51    v2_funct_1(k2_funct_1(sK2)) | ~spl3_16),
% 0.22/0.51    inference(avatar_component_clause,[],[f304])).
% 0.22/0.51  fof(f304,plain,(
% 0.22/0.51    spl3_16 <=> v2_funct_1(k2_funct_1(sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.51  fof(f579,plain,(
% 0.22/0.51    spl3_1 | ~spl3_3 | ~spl3_10 | ~spl3_20),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f578])).
% 0.22/0.51  fof(f578,plain,(
% 0.22/0.51    $false | (spl3_1 | ~spl3_3 | ~spl3_10 | ~spl3_20)),
% 0.22/0.51    inference(subsumption_resolution,[],[f577,f455])).
% 0.22/0.51  fof(f455,plain,(
% 0.22/0.51    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (spl3_1 | ~spl3_3 | ~spl3_10)),
% 0.22/0.51    inference(backward_demodulation,[],[f403,f433])).
% 0.22/0.51  fof(f433,plain,(
% 0.22/0.51    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_3 | ~spl3_10)),
% 0.22/0.51    inference(forward_demodulation,[],[f274,f372])).
% 0.22/0.51  fof(f372,plain,(
% 0.22/0.51    k2_struct_0(sK1) = k2_relat_1(sK2) | (~spl3_3 | ~spl3_10)),
% 0.22/0.51    inference(backward_demodulation,[],[f238,f256])).
% 0.22/0.51  fof(f256,plain,(
% 0.22/0.51    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) | (~spl3_3 | ~spl3_10)),
% 0.22/0.51    inference(resolution,[],[f235,f103])).
% 0.22/0.51  fof(f103,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.51  % (20561)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.51  fof(f235,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) | (~spl3_3 | ~spl3_10)),
% 0.22/0.51    inference(backward_demodulation,[],[f167,f228])).
% 0.22/0.51  fof(f228,plain,(
% 0.22/0.51    k2_struct_0(sK0) = k1_relat_1(sK2) | (~spl3_3 | ~spl3_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f227,f128])).
% 0.22/0.51  fof(f128,plain,(
% 0.22/0.51    v1_relat_1(sK2) | ~spl3_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f127])).
% 0.22/0.51  fof(f127,plain,(
% 0.22/0.51    spl3_3 <=> v1_relat_1(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.51  fof(f227,plain,(
% 0.22/0.51    k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK2) | ~spl3_10),
% 0.22/0.51    inference(subsumption_resolution,[],[f226,f169])).
% 0.22/0.51  fof(f169,plain,(
% 0.22/0.51    v4_relat_1(sK2,k2_struct_0(sK0))),
% 0.22/0.51    inference(resolution,[],[f167,f104])).
% 0.22/0.51  fof(f104,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f52])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.22/0.51    inference(pure_predicate_removal,[],[f13])).
% 0.22/0.51  fof(f13,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.51  fof(f226,plain,(
% 0.22/0.51    k2_struct_0(sK0) = k1_relat_1(sK2) | ~v4_relat_1(sK2,k2_struct_0(sK0)) | ~v1_relat_1(sK2) | ~spl3_10),
% 0.22/0.51    inference(resolution,[],[f184,f95])).
% 0.22/0.51  fof(f95,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | k1_relat_1(X1) = X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f63])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(nnf_transformation,[],[f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(flattening,[],[f48])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,axiom,(
% 0.22/0.51    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 0.22/0.51  fof(f184,plain,(
% 0.22/0.51    v1_partfun1(sK2,k2_struct_0(sK0)) | ~spl3_10),
% 0.22/0.51    inference(avatar_component_clause,[],[f182])).
% 0.22/0.51  fof(f182,plain,(
% 0.22/0.51    spl3_10 <=> v1_partfun1(sK2,k2_struct_0(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.51  fof(f238,plain,(
% 0.22/0.51    k2_struct_0(sK1) = k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) | (~spl3_3 | ~spl3_10)),
% 0.22/0.51    inference(backward_demodulation,[],[f191,f228])).
% 0.22/0.51  fof(f274,plain,(
% 0.22/0.51    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2) | (~spl3_3 | ~spl3_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f273,f70])).
% 0.22/0.51  fof(f273,plain,(
% 0.22/0.51    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2) | ~v1_funct_1(sK2) | (~spl3_3 | ~spl3_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f272,f234])).
% 0.22/0.51  fof(f234,plain,(
% 0.22/0.51    v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1)) | (~spl3_3 | ~spl3_10)),
% 0.22/0.51    inference(backward_demodulation,[],[f165,f228])).
% 0.22/0.51  fof(f272,plain,(
% 0.22/0.51    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | (~spl3_3 | ~spl3_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f271,f235])).
% 0.22/0.51  fof(f271,plain,(
% 0.22/0.51    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | (~spl3_3 | ~spl3_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f270,f74])).
% 0.22/0.51  fof(f270,plain,(
% 0.22/0.51    ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | (~spl3_3 | ~spl3_10)),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f263])).
% 0.22/0.51  fof(f263,plain,(
% 0.22/0.51    k2_struct_0(sK1) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | (~spl3_3 | ~spl3_10)),
% 0.22/0.51    inference(superposition,[],[f108,f238])).
% 0.22/0.51  fof(f108,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f56])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.51    inference(flattening,[],[f55])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.51    inference(ennf_transformation,[],[f23])).
% 0.22/0.51  fof(f23,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 0.22/0.51  fof(f403,plain,(
% 0.22/0.51    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | (spl3_1 | ~spl3_3 | ~spl3_10)),
% 0.22/0.51    inference(backward_demodulation,[],[f239,f372])).
% 0.22/0.51  fof(f239,plain,(
% 0.22/0.51    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)) | (spl3_1 | ~spl3_3 | ~spl3_10)),
% 0.22/0.51    inference(backward_demodulation,[],[f225,f228])).
% 0.22/0.51  fof(f225,plain,(
% 0.22/0.51    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | spl3_1),
% 0.22/0.51    inference(forward_demodulation,[],[f224,f123])).
% 0.22/0.51  fof(f224,plain,(
% 0.22/0.51    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | spl3_1),
% 0.22/0.51    inference(forward_demodulation,[],[f117,f124])).
% 0.22/0.51  fof(f117,plain,(
% 0.22/0.51    k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | spl3_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f115])).
% 0.22/0.51  fof(f115,plain,(
% 0.22/0.51    spl3_1 <=> k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.51  fof(f577,plain,(
% 0.22/0.51    k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_3 | ~spl3_10 | ~spl3_20)),
% 0.22/0.51    inference(forward_demodulation,[],[f459,f366])).
% 0.22/0.51  fof(f366,plain,(
% 0.22/0.51    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_20),
% 0.22/0.51    inference(avatar_component_clause,[],[f364])).
% 0.22/0.51  fof(f459,plain,(
% 0.22/0.51    k1_relat_1(k2_funct_1(sK2)) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_3 | ~spl3_10)),
% 0.22/0.51    inference(resolution,[],[f434,f102])).
% 0.22/0.51  fof(f102,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f50])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.51  fof(f434,plain,(
% 0.22/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | (~spl3_3 | ~spl3_10)),
% 0.22/0.51    inference(forward_demodulation,[],[f282,f372])).
% 0.22/0.51  fof(f282,plain,(
% 0.22/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2)))) | (~spl3_3 | ~spl3_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f281,f70])).
% 0.22/0.51  fof(f281,plain,(
% 0.22/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2)))) | ~v1_funct_1(sK2) | (~spl3_3 | ~spl3_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f280,f234])).
% 0.22/0.51  fof(f280,plain,(
% 0.22/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | (~spl3_3 | ~spl3_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f279,f235])).
% 0.22/0.51  fof(f279,plain,(
% 0.22/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | (~spl3_3 | ~spl3_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f267,f74])).
% 0.22/0.51  fof(f267,plain,(
% 0.22/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2)))) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | (~spl3_3 | ~spl3_10)),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f266])).
% 0.22/0.51  fof(f266,plain,(
% 0.22/0.51    k2_struct_0(sK1) != k2_struct_0(sK1) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2)))) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | (~spl3_3 | ~spl3_10)),
% 0.22/0.51    inference(superposition,[],[f107,f238])).
% 0.22/0.51  fof(f107,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f54])).
% 0.22/0.51  fof(f547,plain,(
% 0.22/0.51    spl3_2 | ~spl3_3 | ~spl3_10 | ~spl3_17),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f546])).
% 0.22/0.51  fof(f546,plain,(
% 0.22/0.51    $false | (spl3_2 | ~spl3_3 | ~spl3_10 | ~spl3_17)),
% 0.22/0.51    inference(subsumption_resolution,[],[f545,f228])).
% 0.22/0.51  fof(f545,plain,(
% 0.22/0.51    k2_struct_0(sK0) != k1_relat_1(sK2) | (spl3_2 | ~spl3_3 | ~spl3_10 | ~spl3_17)),
% 0.22/0.51    inference(forward_demodulation,[],[f544,f464])).
% 0.22/0.51  fof(f464,plain,(
% 0.22/0.51    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_3 | ~spl3_10 | ~spl3_17)),
% 0.22/0.51    inference(forward_demodulation,[],[f458,f309])).
% 0.22/0.51  fof(f309,plain,(
% 0.22/0.51    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_17),
% 0.22/0.51    inference(avatar_component_clause,[],[f308])).
% 0.22/0.51  fof(f308,plain,(
% 0.22/0.51    spl3_17 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.51  fof(f458,plain,(
% 0.22/0.51    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_3 | ~spl3_10)),
% 0.22/0.51    inference(resolution,[],[f434,f103])).
% 0.22/0.51  fof(f544,plain,(
% 0.22/0.51    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (spl3_2 | ~spl3_3 | ~spl3_10)),
% 0.22/0.51    inference(forward_demodulation,[],[f543,f433])).
% 0.22/0.51  fof(f543,plain,(
% 0.22/0.51    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | (spl3_2 | ~spl3_3 | ~spl3_10)),
% 0.22/0.51    inference(forward_demodulation,[],[f542,f233])).
% 0.22/0.51  fof(f233,plain,(
% 0.22/0.51    u1_struct_0(sK0) = k1_relat_1(sK2) | (~spl3_3 | ~spl3_10)),
% 0.22/0.51    inference(backward_demodulation,[],[f123,f228])).
% 0.22/0.51  fof(f542,plain,(
% 0.22/0.51    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)) | (spl3_2 | ~spl3_3 | ~spl3_10)),
% 0.22/0.51    inference(forward_demodulation,[],[f121,f399])).
% 0.22/0.51  fof(f399,plain,(
% 0.22/0.51    u1_struct_0(sK1) = k2_relat_1(sK2) | (~spl3_3 | ~spl3_10)),
% 0.22/0.51    inference(backward_demodulation,[],[f124,f372])).
% 0.22/0.51  fof(f121,plain,(
% 0.22/0.51    k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | spl3_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f119])).
% 0.22/0.51  fof(f119,plain,(
% 0.22/0.51    spl3_2 <=> k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.51  fof(f352,plain,(
% 0.22/0.51    ~spl3_4 | ~spl3_6 | ~spl3_8 | ~spl3_16 | spl3_17),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f351])).
% 0.22/0.51  fof(f351,plain,(
% 0.22/0.51    $false | (~spl3_4 | ~spl3_6 | ~spl3_8 | ~spl3_16 | spl3_17)),
% 0.22/0.51    inference(subsumption_resolution,[],[f350,f310])).
% 0.22/0.51  fof(f310,plain,(
% 0.22/0.51    k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | spl3_17),
% 0.22/0.51    inference(avatar_component_clause,[],[f308])).
% 0.22/0.51  fof(f350,plain,(
% 0.22/0.51    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl3_4 | ~spl3_6 | ~spl3_8 | ~spl3_16)),
% 0.22/0.51    inference(forward_demodulation,[],[f346,f77])).
% 0.22/0.51  fof(f346,plain,(
% 0.22/0.51    k2_relat_1(k2_funct_1(sK2)) = k2_relat_1(k6_relat_1(k1_relat_1(sK2))) | (~spl3_4 | ~spl3_6 | ~spl3_8 | ~spl3_16)),
% 0.22/0.51    inference(superposition,[],[f77,f332])).
% 0.22/0.51  fof(f332,plain,(
% 0.22/0.51    k6_relat_1(k1_relat_1(sK2)) = k6_relat_1(k2_relat_1(k2_funct_1(sK2))) | (~spl3_4 | ~spl3_6 | ~spl3_8 | ~spl3_16)),
% 0.22/0.51    inference(forward_demodulation,[],[f331,f150])).
% 0.22/0.51  fof(f150,plain,(
% 0.22/0.51    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) | ~spl3_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f148])).
% 0.22/0.51  fof(f148,plain,(
% 0.22/0.51    spl3_6 <=> k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.51  fof(f331,plain,(
% 0.22/0.51    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k2_relat_1(k2_funct_1(sK2))) | (~spl3_4 | ~spl3_8 | ~spl3_16)),
% 0.22/0.51    inference(forward_demodulation,[],[f330,f162])).
% 0.22/0.51  fof(f330,plain,(
% 0.22/0.51    k5_relat_1(k2_funct_1(k2_funct_1(sK2)),k2_funct_1(sK2)) = k6_relat_1(k2_relat_1(k2_funct_1(sK2))) | (~spl3_4 | ~spl3_16)),
% 0.22/0.51    inference(subsumption_resolution,[],[f329,f133])).
% 0.22/0.51  fof(f329,plain,(
% 0.22/0.51    k5_relat_1(k2_funct_1(k2_funct_1(sK2)),k2_funct_1(sK2)) = k6_relat_1(k2_relat_1(k2_funct_1(sK2))) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl3_16),
% 0.22/0.51    inference(subsumption_resolution,[],[f319,f209])).
% 0.22/0.51  fof(f319,plain,(
% 0.22/0.51    k5_relat_1(k2_funct_1(k2_funct_1(sK2)),k2_funct_1(sK2)) = k6_relat_1(k2_relat_1(k2_funct_1(sK2))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl3_16),
% 0.22/0.51    inference(resolution,[],[f305,f89])).
% 0.22/0.51  fof(f89,plain,(
% 0.22/0.51    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f41])).
% 0.22/0.51  fof(f316,plain,(
% 0.22/0.51    ~spl3_3 | spl3_16),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f315])).
% 0.22/0.51  fof(f315,plain,(
% 0.22/0.51    $false | (~spl3_3 | spl3_16)),
% 0.22/0.51    inference(subsumption_resolution,[],[f314,f128])).
% 0.22/0.51  fof(f314,plain,(
% 0.22/0.51    ~v1_relat_1(sK2) | spl3_16),
% 0.22/0.51    inference(subsumption_resolution,[],[f313,f70])).
% 0.22/0.51  fof(f313,plain,(
% 0.22/0.51    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_16),
% 0.22/0.51    inference(subsumption_resolution,[],[f312,f74])).
% 0.22/0.51  fof(f312,plain,(
% 0.22/0.51    ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_16),
% 0.22/0.51    inference(resolution,[],[f306,f84])).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).
% 0.22/0.52  fof(f306,plain,(
% 0.22/0.52    ~v2_funct_1(k2_funct_1(sK2)) | spl3_16),
% 0.22/0.52    inference(avatar_component_clause,[],[f304])).
% 0.22/0.52  fof(f221,plain,(
% 0.22/0.52    ~spl3_9),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f220])).
% 0.22/0.52  fof(f220,plain,(
% 0.22/0.52    $false | ~spl3_9),
% 0.22/0.52    inference(subsumption_resolution,[],[f219,f68])).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    ~v2_struct_0(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f62])).
% 0.22/0.52  fof(f219,plain,(
% 0.22/0.52    v2_struct_0(sK1) | ~spl3_9),
% 0.22/0.52    inference(subsumption_resolution,[],[f218,f69])).
% 0.22/0.52  fof(f218,plain,(
% 0.22/0.52    ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl3_9),
% 0.22/0.52    inference(resolution,[],[f180,f81])).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f22])).
% 0.22/0.52  fof(f22,axiom,(
% 0.22/0.52    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).
% 0.22/0.52  fof(f180,plain,(
% 0.22/0.52    v1_xboole_0(k2_struct_0(sK1)) | ~spl3_9),
% 0.22/0.52    inference(avatar_component_clause,[],[f178])).
% 0.22/0.52  fof(f178,plain,(
% 0.22/0.52    spl3_9 <=> v1_xboole_0(k2_struct_0(sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.52  fof(f188,plain,(
% 0.22/0.52    spl3_3),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f187])).
% 0.22/0.52  fof(f187,plain,(
% 0.22/0.52    $false | spl3_3),
% 0.22/0.52    inference(subsumption_resolution,[],[f186,f91])).
% 0.22/0.52  fof(f91,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.52  fof(f186,plain,(
% 0.22/0.52    ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) | spl3_3),
% 0.22/0.52    inference(subsumption_resolution,[],[f174,f129])).
% 0.22/0.52  fof(f129,plain,(
% 0.22/0.52    ~v1_relat_1(sK2) | spl3_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f127])).
% 0.22/0.52  fof(f174,plain,(
% 0.22/0.52    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))),
% 0.22/0.52    inference(resolution,[],[f167,f80])).
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.52  fof(f185,plain,(
% 0.22/0.52    spl3_9 | spl3_10),
% 0.22/0.52    inference(avatar_split_clause,[],[f176,f182,f178])).
% 0.22/0.52  fof(f176,plain,(
% 0.22/0.52    v1_partfun1(sK2,k2_struct_0(sK0)) | v1_xboole_0(k2_struct_0(sK1))),
% 0.22/0.52    inference(subsumption_resolution,[],[f175,f70])).
% 0.22/0.52  fof(f175,plain,(
% 0.22/0.52    ~v1_funct_1(sK2) | v1_partfun1(sK2,k2_struct_0(sK0)) | v1_xboole_0(k2_struct_0(sK1))),
% 0.22/0.52    inference(subsumption_resolution,[],[f172,f165])).
% 0.22/0.52  fof(f172,plain,(
% 0.22/0.52    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | v1_partfun1(sK2,k2_struct_0(sK0)) | v1_xboole_0(k2_struct_0(sK1))),
% 0.22/0.52    inference(resolution,[],[f167,f93])).
% 0.22/0.52  fof(f93,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_partfun1(X2,X0) | v1_xboole_0(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f45])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.52    inference(flattening,[],[f44])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,axiom,(
% 0.22/0.52    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.22/0.52  fof(f163,plain,(
% 0.22/0.52    ~spl3_3 | spl3_8),
% 0.22/0.52    inference(avatar_split_clause,[],[f158,f160,f127])).
% 0.22/0.52  fof(f158,plain,(
% 0.22/0.52    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f138,f70])).
% 0.22/0.52  fof(f138,plain,(
% 0.22/0.52    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.22/0.52    inference(resolution,[],[f74,f87])).
% 0.22/0.52  fof(f87,plain,(
% 0.22/0.52    ( ! [X0] : (~v2_funct_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,axiom,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).
% 0.22/0.52  fof(f157,plain,(
% 0.22/0.52    ~spl3_3 | spl3_7),
% 0.22/0.52    inference(avatar_split_clause,[],[f152,f154,f127])).
% 0.22/0.52  fof(f152,plain,(
% 0.22/0.52    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f137,f70])).
% 0.22/0.52  fof(f137,plain,(
% 0.22/0.52    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.22/0.52    inference(resolution,[],[f74,f89])).
% 0.22/0.52  fof(f151,plain,(
% 0.22/0.52    ~spl3_3 | spl3_6),
% 0.22/0.52    inference(avatar_split_clause,[],[f146,f148,f127])).
% 0.22/0.52  fof(f146,plain,(
% 0.22/0.52    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f136,f70])).
% 0.22/0.52  fof(f136,plain,(
% 0.22/0.52    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.22/0.52    inference(resolution,[],[f74,f88])).
% 0.22/0.52  fof(f134,plain,(
% 0.22/0.52    ~spl3_3 | spl3_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f125,f131,f127])).
% 0.22/0.52  fof(f125,plain,(
% 0.22/0.52    v1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.22/0.52    inference(resolution,[],[f70,f85])).
% 0.22/0.52  fof(f85,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.22/0.52  fof(f122,plain,(
% 0.22/0.52    ~spl3_1 | ~spl3_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f75,f119,f115])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.22/0.52    inference(cnf_transformation,[],[f62])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (20552)------------------------------
% 0.22/0.52  % (20552)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (20552)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (20552)Memory used [KB]: 10874
% 0.22/0.52  % (20552)Time elapsed: 0.095 s
% 0.22/0.52  % (20552)------------------------------
% 0.22/0.52  % (20552)------------------------------
% 0.22/0.52  % (20562)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (20557)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.52  % (20550)Success in time 0.151 s
%------------------------------------------------------------------------------
