%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1338+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:18 EST 2020

% Result     : Theorem 11.30s
% Output     : Refutation 11.30s
% Verified   : 
% Statistics : Number of formulae       :  169 (1596 expanded)
%              Number of leaves         :   26 ( 328 expanded)
%              Depth                    :   26
%              Number of atoms          :  529 (8594 expanded)
%              Number of equality atoms :  125 (2772 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9450,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f5109,f5189,f5288,f5327,f5427,f5575,f7135,f7227,f7250,f7286,f7290,f7760,f9449])).

fof(f9449,plain,
    ( ~ spl211_6
    | spl211_26
    | ~ spl211_110 ),
    inference(avatar_contradiction_clause,[],[f9448])).

fof(f9448,plain,
    ( $false
    | ~ spl211_6
    | spl211_26
    | ~ spl211_110 ),
    inference(subsumption_resolution,[],[f9447,f5130])).

fof(f5130,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f3412,f3554])).

fof(f3554,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f2571])).

fof(f2571,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1210])).

fof(f1210,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f3412,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f2479])).

fof(f2479,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f2478])).

fof(f2478,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2410])).

fof(f2410,negated_conjecture,(
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
                    & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                 => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                    & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f2409])).

fof(f2409,conjecture,(
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
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
               => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                  & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).

fof(f9447,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl211_6
    | spl211_26
    | ~ spl211_110 ),
    inference(subsumption_resolution,[],[f9446,f3414])).

fof(f3414,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f2479])).

fof(f9446,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl211_6
    | spl211_26
    | ~ spl211_110 ),
    inference(subsumption_resolution,[],[f9445,f3410])).

fof(f3410,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f2479])).

fof(f9445,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl211_6
    | spl211_26
    | ~ spl211_110 ),
    inference(trivial_inequality_removal,[],[f9443])).

fof(f9443,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl211_6
    | spl211_26
    | ~ spl211_110 ),
    inference(superposition,[],[f7163,f4112])).

fof(f4112,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2794])).

fof(f2794,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f2793])).

fof(f2793,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1026])).

fof(f1026,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f7163,plain,
    ( k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | ~ spl211_6
    | spl211_26
    | ~ spl211_110 ),
    inference(backward_demodulation,[],[f7080,f6796])).

fof(f6796,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl211_110 ),
    inference(avatar_component_clause,[],[f6794])).

fof(f6794,plain,
    ( spl211_110
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl211_110])])).

fof(f7080,plain,
    ( k2_struct_0(sK0) != k2_relat_1(k2_funct_1(sK2))
    | ~ spl211_6
    | spl211_26 ),
    inference(subsumption_resolution,[],[f7079,f3410])).

fof(f7079,plain,
    ( k2_struct_0(sK0) != k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl211_6
    | spl211_26 ),
    inference(subsumption_resolution,[],[f7078,f3414])).

fof(f7078,plain,
    ( k2_struct_0(sK0) != k2_relat_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl211_6
    | spl211_26 ),
    inference(subsumption_resolution,[],[f7077,f5969])).

fof(f5969,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl211_6 ),
    inference(backward_demodulation,[],[f5538,f5944])).

fof(f5944,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl211_6 ),
    inference(subsumption_resolution,[],[f5934,f5519])).

fof(f5519,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2)))) ),
    inference(backward_demodulation,[],[f3412,f5517])).

fof(f5517,plain,(
    u1_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f5474,f3416])).

fof(f3416,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f2479])).

fof(f5474,plain,
    ( u1_struct_0(sK1) = k2_relat_1(sK2)
    | ~ l1_struct_0(sK1) ),
    inference(superposition,[],[f3547,f5392])).

fof(f5392,plain,(
    k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f5387,f3412])).

fof(f5387,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(superposition,[],[f3413,f3539])).

fof(f3539,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2554])).

fof(f2554,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1228])).

fof(f1228,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f3413,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f2479])).

fof(f3547,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2562])).

fof(f2562,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1773])).

fof(f1773,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f5934,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl211_6 ),
    inference(superposition,[],[f5527,f3463])).

fof(f3463,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2496])).

fof(f2496,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1227])).

fof(f1227,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f5527,plain,
    ( u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl211_6 ),
    inference(backward_demodulation,[],[f5170,f5517])).

fof(f5170,plain,
    ( u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl211_6 ),
    inference(avatar_component_clause,[],[f5168])).

fof(f5168,plain,
    ( spl211_6
  <=> u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl211_6])])).

fof(f5538,plain,(
    k2_relat_1(sK2) = k2_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(backward_demodulation,[],[f5394,f5517])).

fof(f5394,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f3413,f5392])).

fof(f7077,plain,
    ( k2_struct_0(sK0) != k2_relat_1(k2_funct_1(sK2))
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl211_6
    | spl211_26 ),
    inference(subsumption_resolution,[],[f7076,f5956])).

fof(f5956,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl211_6 ),
    inference(backward_demodulation,[],[f5519,f5944])).

fof(f7076,plain,
    ( k2_struct_0(sK0) != k2_relat_1(k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl211_6
    | spl211_26 ),
    inference(subsumption_resolution,[],[f7074,f5955])).

fof(f5955,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl211_6 ),
    inference(backward_demodulation,[],[f5518,f5944])).

fof(f5518,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f3411,f5517])).

fof(f3411,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f2479])).

fof(f7074,plain,
    ( k2_struct_0(sK0) != k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl211_6
    | spl211_26 ),
    inference(superposition,[],[f5972,f3472])).

fof(f3472,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f2505])).

fof(f2505,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f2504])).

fof(f2504,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f5972,plain,
    ( k2_struct_0(sK0) != k2_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | ~ spl211_6
    | spl211_26 ),
    inference(backward_demodulation,[],[f5542,f5944])).

fof(f5542,plain,
    ( k2_struct_0(sK0) != k2_relat_1(k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2))
    | spl211_26 ),
    inference(backward_demodulation,[],[f5426,f5517])).

fof(f5426,plain,
    ( k2_struct_0(sK0) != k2_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | spl211_26 ),
    inference(avatar_component_clause,[],[f5424])).

fof(f5424,plain,
    ( spl211_26
  <=> k2_struct_0(sK0) = k2_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl211_26])])).

fof(f7760,plain,
    ( ~ spl211_6
    | ~ spl211_109
    | spl211_131 ),
    inference(avatar_contradiction_clause,[],[f7759])).

fof(f7759,plain,
    ( $false
    | ~ spl211_6
    | ~ spl211_109
    | spl211_131 ),
    inference(subsumption_resolution,[],[f7758,f3410])).

fof(f7758,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl211_6
    | ~ spl211_109
    | spl211_131 ),
    inference(subsumption_resolution,[],[f7757,f3414])).

fof(f7757,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl211_6
    | ~ spl211_109
    | spl211_131 ),
    inference(subsumption_resolution,[],[f7756,f5969])).

fof(f7756,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl211_6
    | ~ spl211_109
    | spl211_131 ),
    inference(subsumption_resolution,[],[f7755,f5956])).

fof(f7755,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl211_6
    | ~ spl211_109
    | spl211_131 ),
    inference(subsumption_resolution,[],[f7754,f5955])).

fof(f7754,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl211_109
    | spl211_131 ),
    inference(subsumption_resolution,[],[f7752,f6780])).

fof(f6780,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl211_109 ),
    inference(avatar_component_clause,[],[f6779])).

fof(f6779,plain,
    ( spl211_109
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl211_109])])).

fof(f7752,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | spl211_131 ),
    inference(superposition,[],[f7277,f3472])).

fof(f7277,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | spl211_131 ),
    inference(avatar_component_clause,[],[f7275])).

fof(f7275,plain,
    ( spl211_131
  <=> k2_relat_1(sK2) = k1_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl211_131])])).

fof(f7290,plain,
    ( ~ spl211_6
    | ~ spl211_25
    | spl211_130 ),
    inference(avatar_contradiction_clause,[],[f7289])).

fof(f7289,plain,
    ( $false
    | ~ spl211_6
    | ~ spl211_25
    | spl211_130 ),
    inference(subsumption_resolution,[],[f7273,f7288])).

fof(f7288,plain,
    ( m1_subset_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl211_6
    | ~ spl211_25 ),
    inference(forward_demodulation,[],[f7287,f5517])).

fof(f7287,plain,
    ( m1_subset_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2))))
    | ~ spl211_6
    | ~ spl211_25 ),
    inference(forward_demodulation,[],[f5421,f5944])).

fof(f5421,plain,
    ( m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl211_25 ),
    inference(avatar_component_clause,[],[f5420])).

fof(f5420,plain,
    ( spl211_25
  <=> m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl211_25])])).

fof(f7273,plain,
    ( ~ m1_subset_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | spl211_130 ),
    inference(avatar_component_clause,[],[f7271])).

fof(f7271,plain,
    ( spl211_130
  <=> m1_subset_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl211_130])])).

fof(f7286,plain,
    ( ~ spl211_131
    | ~ spl211_130
    | spl211_2
    | ~ spl211_6 ),
    inference(avatar_split_clause,[],[f7285,f5168,f5106,f7271,f7275])).

fof(f5106,plain,
    ( spl211_2
  <=> k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl211_2])])).

fof(f7285,plain,
    ( ~ m1_subset_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | k2_relat_1(sK2) != k1_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | spl211_2
    | ~ spl211_6 ),
    inference(forward_demodulation,[],[f7284,f5517])).

fof(f7284,plain,
    ( ~ m1_subset_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2))))
    | k2_relat_1(sK2) != k1_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | spl211_2
    | ~ spl211_6 ),
    inference(forward_demodulation,[],[f7283,f5944])).

fof(f7283,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | spl211_2
    | ~ spl211_6 ),
    inference(forward_demodulation,[],[f7282,f5944])).

fof(f7282,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | spl211_2 ),
    inference(forward_demodulation,[],[f5430,f5517])).

fof(f5430,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | spl211_2 ),
    inference(superposition,[],[f5395,f3463])).

fof(f5395,plain,
    ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_relat_1(sK2)
    | spl211_2 ),
    inference(backward_demodulation,[],[f5108,f5392])).

fof(f5108,plain,
    ( k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | spl211_2 ),
    inference(avatar_component_clause,[],[f5106])).

fof(f7250,plain,
    ( ~ spl211_6
    | spl211_25 ),
    inference(avatar_contradiction_clause,[],[f7249])).

fof(f7249,plain,
    ( $false
    | ~ spl211_6
    | spl211_25 ),
    inference(subsumption_resolution,[],[f7248,f3410])).

fof(f7248,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl211_6
    | spl211_25 ),
    inference(subsumption_resolution,[],[f7247,f5956])).

fof(f7247,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_1(sK2)
    | ~ spl211_6
    | spl211_25 ),
    inference(subsumption_resolution,[],[f7232,f5955])).

fof(f7232,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_1(sK2)
    | ~ spl211_6
    | spl211_25 ),
    inference(resolution,[],[f5971,f3475])).

fof(f3475,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f2507])).

fof(f2507,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f2506])).

fof(f2506,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(f5971,plain,
    ( ~ m1_subset_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl211_6
    | spl211_25 ),
    inference(backward_demodulation,[],[f5541,f5944])).

fof(f5541,plain,
    ( ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),u1_struct_0(sK0))))
    | spl211_25 ),
    inference(backward_demodulation,[],[f5422,f5517])).

fof(f5422,plain,
    ( ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | spl211_25 ),
    inference(avatar_component_clause,[],[f5420])).

fof(f7227,plain,(
    spl211_109 ),
    inference(avatar_contradiction_clause,[],[f7226])).

fof(f7226,plain,
    ( $false
    | spl211_109 ),
    inference(subsumption_resolution,[],[f7225,f5130])).

fof(f7225,plain,
    ( ~ v1_relat_1(sK2)
    | spl211_109 ),
    inference(subsumption_resolution,[],[f7224,f3414])).

fof(f7224,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl211_109 ),
    inference(subsumption_resolution,[],[f7223,f3410])).

fof(f7223,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl211_109 ),
    inference(trivial_inequality_removal,[],[f7219])).

fof(f7219,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl211_109 ),
    inference(superposition,[],[f6781,f4111])).

fof(f4111,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2794])).

fof(f6781,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | spl211_109 ),
    inference(avatar_component_clause,[],[f6779])).

fof(f7135,plain,
    ( ~ spl211_6
    | spl211_110 ),
    inference(avatar_contradiction_clause,[],[f7134])).

fof(f7134,plain,
    ( $false
    | ~ spl211_6
    | spl211_110 ),
    inference(subsumption_resolution,[],[f7133,f3417])).

fof(f3417,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f2479])).

fof(f7133,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl211_6
    | spl211_110 ),
    inference(subsumption_resolution,[],[f7132,f5944])).

fof(f7132,plain,
    ( u1_struct_0(sK0) != k1_relat_1(sK2)
    | ~ l1_struct_0(sK0)
    | spl211_110 ),
    inference(superposition,[],[f6795,f3547])).

fof(f6795,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | spl211_110 ),
    inference(avatar_component_clause,[],[f6794])).

fof(f5575,plain,(
    ~ spl211_18 ),
    inference(avatar_contradiction_clause,[],[f5574])).

fof(f5574,plain,
    ( $false
    | ~ spl211_18 ),
    inference(subsumption_resolution,[],[f5572,f5243])).

fof(f5243,plain,
    ( v1_xboole_0(sK2)
    | ~ spl211_18 ),
    inference(avatar_component_clause,[],[f5242])).

fof(f5242,plain,
    ( spl211_18
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl211_18])])).

fof(f5572,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(resolution,[],[f5487,f4443])).

fof(f4443,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f3084])).

fof(f3084,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f681])).

fof(f681,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

fof(f5487,plain,(
    ~ v1_xboole_0(k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f5486,f3415])).

fof(f3415,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f2479])).

fof(f5486,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f5472,f3416])).

fof(f5472,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(superposition,[],[f3544,f5392])).

fof(f3544,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2559])).

fof(f2559,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2558])).

fof(f2558,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1800])).

fof(f1800,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f5427,plain,
    ( ~ spl211_25
    | ~ spl211_26
    | spl211_1 ),
    inference(avatar_split_clause,[],[f5413,f5102,f5424,f5420])).

fof(f5102,plain,
    ( spl211_1
  <=> k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl211_1])])).

fof(f5413,plain,
    ( k2_struct_0(sK0) != k2_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | spl211_1 ),
    inference(superposition,[],[f5104,f3539])).

fof(f5104,plain,
    ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | spl211_1 ),
    inference(avatar_component_clause,[],[f5102])).

fof(f5327,plain,
    ( ~ spl211_4
    | spl211_23 ),
    inference(avatar_contradiction_clause,[],[f5326])).

fof(f5326,plain,
    ( $false
    | ~ spl211_4
    | spl211_23 ),
    inference(subsumption_resolution,[],[f5325,f4071])).

fof(f4071,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f5325,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl211_4
    | spl211_23 ),
    inference(forward_demodulation,[],[f5310,f4981])).

fof(f4981,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f3919])).

fof(f3919,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f329])).

fof(f329,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f5310,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))
    | ~ spl211_4
    | spl211_23 ),
    inference(backward_demodulation,[],[f5283,f5161])).

fof(f5161,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl211_4 ),
    inference(avatar_component_clause,[],[f5159])).

fof(f5159,plain,
    ( spl211_4
  <=> k1_xboole_0 = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl211_4])])).

fof(f5283,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | spl211_23 ),
    inference(avatar_component_clause,[],[f5281])).

fof(f5281,plain,
    ( spl211_23
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl211_23])])).

fof(f5288,plain,
    ( spl211_18
    | ~ spl211_23 ),
    inference(avatar_split_clause,[],[f5148,f5281,f5242])).

fof(f5148,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f3412,f4060])).

fof(f4060,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f2754])).

fof(f2754,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f541])).

fof(f541,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f5189,plain,
    ( spl211_6
    | spl211_4 ),
    inference(avatar_split_clause,[],[f5188,f5159,f5168])).

fof(f5188,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(subsumption_resolution,[],[f5120,f3411])).

fof(f5120,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(resolution,[],[f3412,f3461])).

fof(f3461,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f2494])).

fof(f2494,plain,(
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
    inference(flattening,[],[f2493])).

fof(f2493,plain,(
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
    inference(ennf_transformation,[],[f1483])).

fof(f1483,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f5109,plain,
    ( ~ spl211_1
    | ~ spl211_2 ),
    inference(avatar_split_clause,[],[f3409,f5106,f5102])).

fof(f3409,plain,
    ( k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f2479])).
%------------------------------------------------------------------------------
