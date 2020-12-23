%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  251 (3095 expanded)
%              Number of leaves         :   30 ( 633 expanded)
%              Depth                    :   31
%              Number of atoms          : 1055 (15899 expanded)
%              Number of equality atoms :  157 (2627 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f633,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f115,f125,f135,f160,f205,f226,f314,f336,f343,f385,f555,f561,f573,f632])).

fof(f632,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | spl3_7
    | ~ spl3_9
    | ~ spl3_20 ),
    inference(avatar_contradiction_clause,[],[f631])).

fof(f631,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | spl3_7
    | ~ spl3_9
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f630,f47])).

fof(f47,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).

fof(f630,plain,
    ( ~ v2_funct_1(sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | spl3_7
    | ~ spl3_9
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f629,f136])).

fof(f136,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f98,f65])).

fof(f65,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f98,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f45,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f20])).

fof(f629,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | spl3_7
    | ~ spl3_9
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f628,f43])).

fof(f43,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f628,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | spl3_7
    | ~ spl3_9
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f627,f54])).

fof(f54,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f627,plain,
    ( ~ v2_funct_1(k6_relat_1(k2_relat_1(sK2)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | spl3_7
    | ~ spl3_9
    | ~ spl3_20 ),
    inference(trivial_inequality_removal,[],[f626])).

fof(f626,plain,
    ( ~ v2_funct_1(k6_relat_1(k2_relat_1(sK2)))
    | ~ v1_funct_1(sK2)
    | k1_relat_1(sK2) != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | spl3_7
    | ~ spl3_9
    | ~ spl3_20 ),
    inference(duplicate_literal_removal,[],[f624])).

fof(f624,plain,
    ( ~ v2_funct_1(k6_relat_1(k2_relat_1(sK2)))
    | ~ v1_funct_1(sK2)
    | k1_relat_1(sK2) != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | spl3_7
    | ~ spl3_9
    | ~ spl3_20 ),
    inference(superposition,[],[f566,f62])).

fof(f62,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f566,plain,
    ( ! [X0] :
        ( ~ v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0))
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != k1_relat_1(sK2)
        | ~ v1_relat_1(X0) )
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | spl3_7
    | ~ spl3_9
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f565,f237])).

fof(f237,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | spl3_7 ),
    inference(subsumption_resolution,[],[f236,f43])).

fof(f236,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | spl3_7 ),
    inference(subsumption_resolution,[],[f235,f47])).

fof(f235,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | spl3_7 ),
    inference(subsumption_resolution,[],[f234,f153])).

fof(f153,plain,(
    k2_relat_1(sK2) = k2_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(backward_demodulation,[],[f144,f145])).

fof(f145,plain,(
    k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f141,f45])).

fof(f141,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(superposition,[],[f46,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f46,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f144,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(subsumption_resolution,[],[f140,f50])).

fof(f50,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f140,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ l1_struct_0(sK1) ),
    inference(superposition,[],[f46,f55])).

fof(f55,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f234,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | k2_relat_1(sK2) != k2_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | spl3_7 ),
    inference(subsumption_resolution,[],[f233,f151])).

fof(f151,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2)))) ),
    inference(backward_demodulation,[],[f138,f145])).

fof(f138,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f100,f50])).

fof(f100,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ l1_struct_0(sK1) ),
    inference(superposition,[],[f45,f55])).

fof(f233,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2))))
    | k2_relat_1(sK2) != k2_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | spl3_7 ),
    inference(subsumption_resolution,[],[f231,f147])).

fof(f147,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f89,f145])).

fof(f89,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f87,f50])).

fof(f87,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ l1_struct_0(sK1) ),
    inference(superposition,[],[f44,f55])).

fof(f44,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f231,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2))))
    | k2_relat_1(sK2) != k2_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | spl3_7 ),
    inference(superposition,[],[f188,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f188,plain,
    ( ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl3_7
  <=> v2_funct_1(k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f565,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != k1_relat_1(sK2)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0))
        | ~ v1_relat_1(X0)
        | v2_funct_1(k2_funct_1(sK2)) )
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f564,f110])).

fof(f110,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl3_1
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f564,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != k1_relat_1(sK2)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_1(k2_funct_1(sK2))
        | ~ v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0))
        | ~ v1_relat_1(X0)
        | v2_funct_1(k2_funct_1(sK2)) )
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f562,f529])).

fof(f529,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f528,f43])).

fof(f528,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f527,f47])).

fof(f527,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f526,f262])).

fof(f262,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f153,f259])).

fof(f259,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f257,f151])).

fof(f257,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(superposition,[],[f168,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f168,plain,
    ( u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f130,f162])).

fof(f162,plain,
    ( u1_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f113,f145])).

fof(f113,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl3_2
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f130,plain,
    ( u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl3_4
  <=> u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f526,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f525,f261])).

fof(f261,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f151,f259])).

fof(f525,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f524,f260])).

fof(f260,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f147,f259])).

fof(f524,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(superposition,[],[f523,f77])).

fof(f523,plain,
    ( v1_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f509,f65])).

fof(f509,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))
    | v1_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(resolution,[],[f337,f56])).

fof(f337,plain,
    ( m1_subset_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f195,f259])).

fof(f195,plain,
    ( m1_subset_1(k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),u1_struct_0(sK0))))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl3_9
  <=> m1_subset_1(k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f562,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != k1_relat_1(sK2)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(k2_funct_1(sK2))
        | ~ v1_funct_1(k2_funct_1(sK2))
        | ~ v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0))
        | ~ v1_relat_1(X0)
        | v2_funct_1(k2_funct_1(sK2)) )
    | ~ spl3_20 ),
    inference(superposition,[],[f63,f553])).

fof(f553,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f552])).

fof(f552,plain,
    ( spl3_20
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X0)
      | v2_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

fof(f573,plain,
    ( ~ spl3_2
    | ~ spl3_4
    | spl3_19 ),
    inference(avatar_contradiction_clause,[],[f572])).

fof(f572,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_4
    | spl3_19 ),
    inference(subsumption_resolution,[],[f571,f43])).

fof(f571,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl3_2
    | ~ spl3_4
    | spl3_19 ),
    inference(subsumption_resolution,[],[f570,f262])).

fof(f570,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_2
    | ~ spl3_4
    | spl3_19 ),
    inference(subsumption_resolution,[],[f569,f47])).

fof(f569,plain,
    ( ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_2
    | ~ spl3_4
    | spl3_19 ),
    inference(subsumption_resolution,[],[f568,f261])).

fof(f568,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_2
    | ~ spl3_4
    | spl3_19 ),
    inference(subsumption_resolution,[],[f567,f260])).

fof(f567,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_funct_1(sK2)
    | spl3_19 ),
    inference(resolution,[],[f550,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f550,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | spl3_19 ),
    inference(avatar_component_clause,[],[f548])).

fof(f548,plain,
    ( spl3_19
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f561,plain,(
    spl3_20 ),
    inference(avatar_contradiction_clause,[],[f560])).

fof(f560,plain,
    ( $false
    | spl3_20 ),
    inference(subsumption_resolution,[],[f559,f136])).

fof(f559,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_20 ),
    inference(subsumption_resolution,[],[f558,f47])).

fof(f558,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_20 ),
    inference(subsumption_resolution,[],[f557,f43])).

fof(f557,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_20 ),
    inference(trivial_inequality_removal,[],[f556])).

fof(f556,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_20 ),
    inference(superposition,[],[f554,f60])).

fof(f60,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f554,plain,
    ( k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | spl3_20 ),
    inference(avatar_component_clause,[],[f552])).

fof(f555,plain,
    ( ~ spl3_19
    | ~ spl3_20
    | ~ spl3_2
    | ~ spl3_4
    | spl3_8 ),
    inference(avatar_split_clause,[],[f546,f190,f128,f112,f552,f548])).

fof(f190,plain,
    ( spl3_8
  <=> u1_struct_0(sK0) = k2_relset_1(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f546,plain,
    ( k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_2
    | ~ spl3_4
    | spl3_8 ),
    inference(superposition,[],[f544,f67])).

fof(f544,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_2
    | ~ spl3_4
    | spl3_8 ),
    inference(subsumption_resolution,[],[f543,f43])).

fof(f543,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_2
    | ~ spl3_4
    | spl3_8 ),
    inference(subsumption_resolution,[],[f542,f47])).

fof(f542,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_2
    | ~ spl3_4
    | spl3_8 ),
    inference(subsumption_resolution,[],[f541,f262])).

fof(f541,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_2
    | ~ spl3_4
    | spl3_8 ),
    inference(subsumption_resolution,[],[f540,f261])).

fof(f540,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_2
    | ~ spl3_4
    | spl3_8 ),
    inference(subsumption_resolution,[],[f538,f260])).

fof(f538,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_2
    | ~ spl3_4
    | spl3_8 ),
    inference(superposition,[],[f270,f77])).

fof(f270,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | ~ spl3_2
    | ~ spl3_4
    | spl3_8 ),
    inference(backward_demodulation,[],[f192,f259])).

fof(f192,plain,
    ( u1_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f190])).

fof(f385,plain,
    ( ~ spl3_2
    | ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f384])).

fof(f384,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f379,f52])).

fof(f52,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f379,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f211,f360])).

fof(f360,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f162,f134])).

fof(f134,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl3_5
  <=> k1_xboole_0 = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f211,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f210,f49])).

fof(f49,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f210,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | v2_struct_0(sK1)
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f208,f50])).

fof(f208,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl3_2 ),
    inference(superposition,[],[f57,f162])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

% (5459)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f343,plain,
    ( ~ spl3_2
    | ~ spl3_4
    | spl3_11 ),
    inference(avatar_contradiction_clause,[],[f342])).

fof(f342,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_4
    | spl3_11 ),
    inference(subsumption_resolution,[],[f341,f136])).

fof(f341,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_2
    | ~ spl3_4
    | spl3_11 ),
    inference(subsumption_resolution,[],[f340,f47])).

fof(f340,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_2
    | ~ spl3_4
    | spl3_11 ),
    inference(subsumption_resolution,[],[f339,f43])).

fof(f339,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_2
    | ~ spl3_4
    | spl3_11 ),
    inference(subsumption_resolution,[],[f338,f265])).

fof(f265,plain,
    ( r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f167,f259])).

fof(f167,plain,
    ( r2_funct_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2,sK2)
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f102,f162])).

fof(f102,plain,(
    r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK2) ),
    inference(subsumption_resolution,[],[f101,f43])).

fof(f101,plain,
    ( ~ v1_funct_1(sK2)
    | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK2) ),
    inference(subsumption_resolution,[],[f93,f44])).

fof(f93,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK2) ),
    inference(resolution,[],[f45,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X0,X1,X2)
      | ~ v1_funct_1(X0)
      | r2_funct_2(X1,X2,X0,X0) ) ),
    inference(duplicate_literal_removal,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,X1,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X0,X1,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_funct_2(X1,X2,X0,X0) ) ),
    inference(condensation,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X2,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

fof(f338,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_2
    | ~ spl3_4
    | spl3_11 ),
    inference(superposition,[],[f329,f58])).

fof(f58,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

fof(f329,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(k2_funct_1(sK2)),sK2)
    | ~ spl3_2
    | ~ spl3_4
    | spl3_11 ),
    inference(subsumption_resolution,[],[f328,f43])).

fof(f328,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(k2_funct_1(sK2)),sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_2
    | ~ spl3_4
    | spl3_11 ),
    inference(subsumption_resolution,[],[f327,f47])).

fof(f327,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(k2_funct_1(sK2)),sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_2
    | ~ spl3_4
    | spl3_11 ),
    inference(subsumption_resolution,[],[f326,f262])).

fof(f326,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(k2_funct_1(sK2)),sK2)
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_2
    | ~ spl3_4
    | spl3_11 ),
    inference(subsumption_resolution,[],[f325,f261])).

fof(f325,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(k2_funct_1(sK2)),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_2
    | ~ spl3_4
    | spl3_11 ),
    inference(subsumption_resolution,[],[f324,f260])).

fof(f324,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(k2_funct_1(sK2)),sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_2
    | ~ spl3_4
    | spl3_11 ),
    inference(superposition,[],[f273,f77])).

fof(f273,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2)
    | ~ spl3_2
    | ~ spl3_4
    | spl3_11 ),
    inference(backward_demodulation,[],[f204,f259])).

fof(f204,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),k2_relat_1(sK2),k2_funct_1(k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f202])).

fof(f202,plain,
    ( spl3_11
  <=> r2_funct_2(u1_struct_0(sK0),k2_relat_1(sK2),k2_funct_1(k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f336,plain,
    ( ~ spl3_2
    | ~ spl3_4
    | spl3_9 ),
    inference(avatar_contradiction_clause,[],[f335])).

fof(f335,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_4
    | spl3_9 ),
    inference(subsumption_resolution,[],[f334,f43])).

fof(f334,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl3_2
    | ~ spl3_4
    | spl3_9 ),
    inference(subsumption_resolution,[],[f333,f262])).

fof(f333,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_2
    | ~ spl3_4
    | spl3_9 ),
    inference(subsumption_resolution,[],[f332,f47])).

fof(f332,plain,
    ( ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_2
    | ~ spl3_4
    | spl3_9 ),
    inference(subsumption_resolution,[],[f331,f261])).

fof(f331,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_2
    | ~ spl3_4
    | spl3_9 ),
    inference(subsumption_resolution,[],[f330,f260])).

fof(f330,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_2
    | ~ spl3_4
    | spl3_9 ),
    inference(resolution,[],[f323,f76])).

fof(f323,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_2
    | ~ spl3_4
    | spl3_9 ),
    inference(subsumption_resolution,[],[f322,f43])).

fof(f322,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_funct_1(sK2)
    | ~ spl3_2
    | ~ spl3_4
    | spl3_9 ),
    inference(subsumption_resolution,[],[f321,f47])).

fof(f321,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_2
    | ~ spl3_4
    | spl3_9 ),
    inference(subsumption_resolution,[],[f320,f262])).

fof(f320,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_2
    | ~ spl3_4
    | spl3_9 ),
    inference(subsumption_resolution,[],[f319,f261])).

fof(f319,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_2
    | ~ spl3_4
    | spl3_9 ),
    inference(subsumption_resolution,[],[f318,f260])).

fof(f318,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_2
    | ~ spl3_4
    | spl3_9 ),
    inference(superposition,[],[f271,f77])).

fof(f271,plain,
    ( ~ m1_subset_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_2
    | ~ spl3_4
    | spl3_9 ),
    inference(backward_demodulation,[],[f196,f259])).

fof(f196,plain,
    ( ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),u1_struct_0(sK0))))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f194])).

fof(f314,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | spl3_10 ),
    inference(avatar_contradiction_clause,[],[f313])).

fof(f313,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | spl3_10 ),
    inference(subsumption_resolution,[],[f312,f43])).

fof(f312,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | spl3_10 ),
    inference(subsumption_resolution,[],[f311,f47])).

fof(f311,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | spl3_10 ),
    inference(subsumption_resolution,[],[f310,f262])).

fof(f310,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | spl3_10 ),
    inference(subsumption_resolution,[],[f309,f261])).

fof(f309,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | spl3_10 ),
    inference(subsumption_resolution,[],[f308,f260])).

fof(f308,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | spl3_10 ),
    inference(subsumption_resolution,[],[f307,f263])).

fof(f263,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f161,f259])).

fof(f161,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),u1_struct_0(sK0))
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f124,f145])).

fof(f124,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl3_3
  <=> v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f307,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_2
    | ~ spl3_4
    | spl3_10 ),
    inference(superposition,[],[f272,f77])).

fof(f272,plain,
    ( ~ v1_funct_2(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl3_2
    | ~ spl3_4
    | spl3_10 ),
    inference(backward_demodulation,[],[f200,f259])).

fof(f200,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2),k2_relat_1(sK2),u1_struct_0(sK0))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl3_10
  <=> v1_funct_2(k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2),k2_relat_1(sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f226,plain,
    ( ~ spl3_1
    | spl3_6 ),
    inference(avatar_contradiction_clause,[],[f225])).

fof(f225,plain,
    ( $false
    | ~ spl3_1
    | spl3_6 ),
    inference(subsumption_resolution,[],[f224,f43])).

fof(f224,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl3_1
    | spl3_6 ),
    inference(subsumption_resolution,[],[f223,f47])).

fof(f223,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_1
    | spl3_6 ),
    inference(subsumption_resolution,[],[f222,f153])).

fof(f222,plain,
    ( k2_relat_1(sK2) != k2_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_1
    | spl3_6 ),
    inference(subsumption_resolution,[],[f221,f151])).

fof(f221,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2))))
    | k2_relat_1(sK2) != k2_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_1
    | spl3_6 ),
    inference(subsumption_resolution,[],[f220,f147])).

fof(f220,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2))))
    | k2_relat_1(sK2) != k2_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_1
    | spl3_6 ),
    inference(subsumption_resolution,[],[f218,f110])).

fof(f218,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2))))
    | k2_relat_1(sK2) != k2_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | spl3_6 ),
    inference(superposition,[],[f184,f77])).

fof(f184,plain,
    ( ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl3_6
  <=> v1_funct_1(k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f205,plain,
    ( ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f174,f112,f202,f198,f194,f190,f186,f182])).

fof(f174,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),k2_relat_1(sK2),k2_funct_1(k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2)
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2),k2_relat_1(sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),u1_struct_0(sK0))))
    | u1_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2))
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2))
    | ~ spl3_2 ),
    inference(superposition,[],[f165,f77])).

fof(f165,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2)
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f48,f162])).

fof(f48,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f160,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f159])).

fof(f159,plain,
    ( $false
    | spl3_2 ),
    inference(subsumption_resolution,[],[f158,f50])).

fof(f158,plain,
    ( ~ l1_struct_0(sK1)
    | spl3_2 ),
    inference(subsumption_resolution,[],[f157,f145])).

fof(f157,plain,
    ( k2_struct_0(sK1) != k2_relat_1(sK2)
    | ~ l1_struct_0(sK1)
    | spl3_2 ),
    inference(superposition,[],[f149,f55])).

fof(f149,plain,
    ( u1_struct_0(sK1) != k2_relat_1(sK2)
    | spl3_2 ),
    inference(backward_demodulation,[],[f114,f145])).

fof(f114,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f112])).

fof(f135,plain,
    ( spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f126,f132,f128])).

fof(f126,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(subsumption_resolution,[],[f97,f44])).

fof(f97,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(resolution,[],[f45,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f125,plain,
    ( spl3_3
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f120,f112,f122])).

fof(f120,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(inner_rewriting,[],[f119])).

fof(f119,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f118,f46])).

fof(f118,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f117,f47])).

fof(f117,plain,
    ( ~ v2_funct_1(sK2)
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f116,f43])).

fof(f116,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f95,f44])).

fof(f95,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f45,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_2(k2_funct_1(X2),X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f115,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f106,f112,f108])).

fof(f106,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f105,f46])).

fof(f105,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f104,f47])).

fof(f104,plain,
    ( ~ v2_funct_1(sK2)
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f103,f43])).

fof(f103,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f94,f44])).

fof(f94,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f45,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_1(k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n005.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:05:02 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (5447)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (5447)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f633,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f115,f125,f135,f160,f205,f226,f314,f336,f343,f385,f555,f561,f573,f632])).
% 0.21/0.49  fof(f632,plain,(
% 0.21/0.49    ~spl3_1 | ~spl3_2 | ~spl3_4 | spl3_7 | ~spl3_9 | ~spl3_20),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f631])).
% 0.21/0.49  fof(f631,plain,(
% 0.21/0.49    $false | (~spl3_1 | ~spl3_2 | ~spl3_4 | spl3_7 | ~spl3_9 | ~spl3_20)),
% 0.21/0.49    inference(subsumption_resolution,[],[f630,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    v2_funct_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.21/0.49    inference(negated_conjecture,[],[f17])).
% 0.21/0.49  fof(f17,conjecture,(
% 0.21/0.49    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).
% 0.21/0.49  fof(f630,plain,(
% 0.21/0.49    ~v2_funct_1(sK2) | (~spl3_1 | ~spl3_2 | ~spl3_4 | spl3_7 | ~spl3_9 | ~spl3_20)),
% 0.21/0.49    inference(subsumption_resolution,[],[f629,f136])).
% 0.21/0.49  fof(f136,plain,(
% 0.21/0.49    v1_relat_1(sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f98,f65])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) | v1_relat_1(sK2)),
% 0.21/0.49    inference(resolution,[],[f45,f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f629,plain,(
% 0.21/0.49    ~v1_relat_1(sK2) | ~v2_funct_1(sK2) | (~spl3_1 | ~spl3_2 | ~spl3_4 | spl3_7 | ~spl3_9 | ~spl3_20)),
% 0.21/0.49    inference(subsumption_resolution,[],[f628,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    v1_funct_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f628,plain,(
% 0.21/0.49    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v2_funct_1(sK2) | (~spl3_1 | ~spl3_2 | ~spl3_4 | spl3_7 | ~spl3_9 | ~spl3_20)),
% 0.21/0.49    inference(subsumption_resolution,[],[f627,f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.21/0.49  fof(f627,plain,(
% 0.21/0.49    ~v2_funct_1(k6_relat_1(k2_relat_1(sK2))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v2_funct_1(sK2) | (~spl3_1 | ~spl3_2 | ~spl3_4 | spl3_7 | ~spl3_9 | ~spl3_20)),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f626])).
% 0.21/0.49  fof(f626,plain,(
% 0.21/0.49    ~v2_funct_1(k6_relat_1(k2_relat_1(sK2))) | ~v1_funct_1(sK2) | k1_relat_1(sK2) != k1_relat_1(sK2) | ~v1_relat_1(sK2) | ~v2_funct_1(sK2) | (~spl3_1 | ~spl3_2 | ~spl3_4 | spl3_7 | ~spl3_9 | ~spl3_20)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f624])).
% 0.21/0.49  fof(f624,plain,(
% 0.21/0.49    ~v2_funct_1(k6_relat_1(k2_relat_1(sK2))) | ~v1_funct_1(sK2) | k1_relat_1(sK2) != k1_relat_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_1 | ~spl3_2 | ~spl3_4 | spl3_7 | ~spl3_9 | ~spl3_20)),
% 0.21/0.49    inference(superposition,[],[f566,f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 0.21/0.49  fof(f566,plain,(
% 0.21/0.49    ( ! [X0] : (~v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0)) | ~v1_funct_1(X0) | k1_relat_1(X0) != k1_relat_1(sK2) | ~v1_relat_1(X0)) ) | (~spl3_1 | ~spl3_2 | ~spl3_4 | spl3_7 | ~spl3_9 | ~spl3_20)),
% 0.21/0.49    inference(subsumption_resolution,[],[f565,f237])).
% 0.21/0.49  fof(f237,plain,(
% 0.21/0.49    ~v2_funct_1(k2_funct_1(sK2)) | spl3_7),
% 0.21/0.49    inference(subsumption_resolution,[],[f236,f43])).
% 0.21/0.49  fof(f236,plain,(
% 0.21/0.49    ~v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | spl3_7),
% 0.21/0.49    inference(subsumption_resolution,[],[f235,f47])).
% 0.21/0.49  fof(f235,plain,(
% 0.21/0.49    ~v2_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | spl3_7),
% 0.21/0.49    inference(subsumption_resolution,[],[f234,f153])).
% 0.21/0.49  fof(f153,plain,(
% 0.21/0.49    k2_relat_1(sK2) = k2_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.21/0.49    inference(backward_demodulation,[],[f144,f145])).
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f141,f45])).
% 0.21/0.49  fof(f141,plain,(
% 0.21/0.49    k2_struct_0(sK1) = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.49    inference(superposition,[],[f46,f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f144,plain,(
% 0.21/0.49    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f140,f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    l1_struct_0(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | ~l1_struct_0(sK1)),
% 0.21/0.49    inference(superposition,[],[f46,f55])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,axiom,(
% 0.21/0.49    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.49  fof(f234,plain,(
% 0.21/0.49    ~v2_funct_1(k2_funct_1(sK2)) | k2_relat_1(sK2) != k2_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | spl3_7),
% 0.21/0.49    inference(subsumption_resolution,[],[f233,f151])).
% 0.21/0.49  fof(f151,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2))))),
% 0.21/0.49    inference(backward_demodulation,[],[f138,f145])).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))),
% 0.21/0.49    inference(subsumption_resolution,[],[f100,f50])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | ~l1_struct_0(sK1)),
% 0.21/0.49    inference(superposition,[],[f45,f55])).
% 0.21/0.49  fof(f233,plain,(
% 0.21/0.49    ~v2_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2)))) | k2_relat_1(sK2) != k2_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | spl3_7),
% 0.21/0.49    inference(subsumption_resolution,[],[f231,f147])).
% 0.21/0.49  fof(f147,plain,(
% 0.21/0.49    v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2))),
% 0.21/0.49    inference(backward_demodulation,[],[f89,f145])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f87,f50])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | ~l1_struct_0(sK1)),
% 0.21/0.49    inference(superposition,[],[f44,f55])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f231,plain,(
% 0.21/0.49    ~v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2)))) | k2_relat_1(sK2) != k2_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | spl3_7),
% 0.21/0.49    inference(superposition,[],[f188,f77])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~v1_funct_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.49    inference(flattening,[],[f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 0.21/0.49  fof(f188,plain,(
% 0.21/0.49    ~v2_funct_1(k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)) | spl3_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f186])).
% 0.21/0.49  fof(f186,plain,(
% 0.21/0.49    spl3_7 <=> v2_funct_1(k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.49  fof(f565,plain,(
% 0.21/0.49    ( ! [X0] : (k1_relat_1(X0) != k1_relat_1(sK2) | ~v1_funct_1(X0) | ~v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0)) | ~v1_relat_1(X0) | v2_funct_1(k2_funct_1(sK2))) ) | (~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_9 | ~spl3_20)),
% 0.21/0.49    inference(subsumption_resolution,[],[f564,f110])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    v1_funct_1(k2_funct_1(sK2)) | ~spl3_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f108])).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    spl3_1 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.49  fof(f564,plain,(
% 0.21/0.49    ( ! [X0] : (k1_relat_1(X0) != k1_relat_1(sK2) | ~v1_funct_1(X0) | ~v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0)) | ~v1_relat_1(X0) | v2_funct_1(k2_funct_1(sK2))) ) | (~spl3_2 | ~spl3_4 | ~spl3_9 | ~spl3_20)),
% 0.21/0.49    inference(subsumption_resolution,[],[f562,f529])).
% 0.21/0.49  fof(f529,plain,(
% 0.21/0.49    v1_relat_1(k2_funct_1(sK2)) | (~spl3_2 | ~spl3_4 | ~spl3_9)),
% 0.21/0.49    inference(subsumption_resolution,[],[f528,f43])).
% 0.21/0.49  fof(f528,plain,(
% 0.21/0.49    v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_2 | ~spl3_4 | ~spl3_9)),
% 0.21/0.49    inference(subsumption_resolution,[],[f527,f47])).
% 0.21/0.49  fof(f527,plain,(
% 0.21/0.49    v1_relat_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | (~spl3_2 | ~spl3_4 | ~spl3_9)),
% 0.21/0.49    inference(subsumption_resolution,[],[f526,f262])).
% 0.21/0.49  fof(f262,plain,(
% 0.21/0.49    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_2 | ~spl3_4)),
% 0.21/0.49    inference(backward_demodulation,[],[f153,f259])).
% 0.21/0.49  fof(f259,plain,(
% 0.21/0.49    u1_struct_0(sK0) = k1_relat_1(sK2) | (~spl3_2 | ~spl3_4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f257,f151])).
% 0.21/0.49  fof(f257,plain,(
% 0.21/0.49    u1_struct_0(sK0) = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2)))) | (~spl3_2 | ~spl3_4)),
% 0.21/0.49    inference(superposition,[],[f168,f66])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.49  fof(f168,plain,(
% 0.21/0.49    u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2) | (~spl3_2 | ~spl3_4)),
% 0.21/0.49    inference(backward_demodulation,[],[f130,f162])).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    u1_struct_0(sK1) = k2_relat_1(sK2) | ~spl3_2),
% 0.21/0.49    inference(forward_demodulation,[],[f113,f145])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f112])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    spl3_2 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~spl3_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f128])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    spl3_4 <=> u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.49  fof(f526,plain,(
% 0.21/0.49    v1_relat_1(k2_funct_1(sK2)) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | (~spl3_2 | ~spl3_4 | ~spl3_9)),
% 0.21/0.49    inference(subsumption_resolution,[],[f525,f261])).
% 0.21/0.49  fof(f261,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_2 | ~spl3_4)),
% 0.21/0.49    inference(backward_demodulation,[],[f151,f259])).
% 0.21/0.49  fof(f525,plain,(
% 0.21/0.49    v1_relat_1(k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | (~spl3_2 | ~spl3_4 | ~spl3_9)),
% 0.21/0.49    inference(subsumption_resolution,[],[f524,f260])).
% 0.21/0.49  fof(f260,plain,(
% 0.21/0.49    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_2 | ~spl3_4)),
% 0.21/0.49    inference(backward_demodulation,[],[f147,f259])).
% 0.21/0.49  fof(f524,plain,(
% 0.21/0.49    v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | (~spl3_2 | ~spl3_4 | ~spl3_9)),
% 0.21/0.49    inference(superposition,[],[f523,f77])).
% 0.21/0.49  fof(f523,plain,(
% 0.21/0.49    v1_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | (~spl3_2 | ~spl3_4 | ~spl3_9)),
% 0.21/0.49    inference(subsumption_resolution,[],[f509,f65])).
% 0.21/0.49  fof(f509,plain,(
% 0.21/0.49    ~v1_relat_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))) | v1_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | (~spl3_2 | ~spl3_4 | ~spl3_9)),
% 0.21/0.49    inference(resolution,[],[f337,f56])).
% 0.21/0.49  fof(f337,plain,(
% 0.21/0.49    m1_subset_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | (~spl3_2 | ~spl3_4 | ~spl3_9)),
% 0.21/0.49    inference(forward_demodulation,[],[f195,f259])).
% 0.21/0.49  fof(f195,plain,(
% 0.21/0.49    m1_subset_1(k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),u1_struct_0(sK0)))) | ~spl3_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f194])).
% 0.21/0.49  fof(f194,plain,(
% 0.21/0.49    spl3_9 <=> m1_subset_1(k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),u1_struct_0(sK0))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.49  fof(f562,plain,(
% 0.21/0.49    ( ! [X0] : (k1_relat_1(X0) != k1_relat_1(sK2) | ~v1_funct_1(X0) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0)) | ~v1_relat_1(X0) | v2_funct_1(k2_funct_1(sK2))) ) | ~spl3_20),
% 0.21/0.49    inference(superposition,[],[f63,f553])).
% 0.21/0.49  fof(f553,plain,(
% 0.21/0.49    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_20),
% 0.21/0.49    inference(avatar_component_clause,[],[f552])).
% 0.21/0.49  fof(f552,plain,(
% 0.21/0.49    spl3_20 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_relat_1(X0) | v2_funct_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).
% 0.21/0.49  fof(f573,plain,(
% 0.21/0.49    ~spl3_2 | ~spl3_4 | spl3_19),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f572])).
% 0.21/0.49  fof(f572,plain,(
% 0.21/0.49    $false | (~spl3_2 | ~spl3_4 | spl3_19)),
% 0.21/0.49    inference(subsumption_resolution,[],[f571,f43])).
% 0.21/0.49  fof(f571,plain,(
% 0.21/0.49    ~v1_funct_1(sK2) | (~spl3_2 | ~spl3_4 | spl3_19)),
% 0.21/0.49    inference(subsumption_resolution,[],[f570,f262])).
% 0.21/0.49  fof(f570,plain,(
% 0.21/0.49    k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_funct_1(sK2) | (~spl3_2 | ~spl3_4 | spl3_19)),
% 0.21/0.49    inference(subsumption_resolution,[],[f569,f47])).
% 0.21/0.49  fof(f569,plain,(
% 0.21/0.49    ~v2_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_funct_1(sK2) | (~spl3_2 | ~spl3_4 | spl3_19)),
% 0.21/0.49    inference(subsumption_resolution,[],[f568,f261])).
% 0.21/0.49  fof(f568,plain,(
% 0.21/0.49    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v2_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_funct_1(sK2) | (~spl3_2 | ~spl3_4 | spl3_19)),
% 0.21/0.49    inference(subsumption_resolution,[],[f567,f260])).
% 0.21/0.49  fof(f567,plain,(
% 0.21/0.49    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v2_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_funct_1(sK2) | spl3_19),
% 0.21/0.49    inference(resolution,[],[f550,f76])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.49    inference(flattening,[],[f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.21/0.49  fof(f550,plain,(
% 0.21/0.49    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | spl3_19),
% 0.21/0.49    inference(avatar_component_clause,[],[f548])).
% 0.21/0.49  fof(f548,plain,(
% 0.21/0.49    spl3_19 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.49  fof(f561,plain,(
% 0.21/0.49    spl3_20),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f560])).
% 0.21/0.49  fof(f560,plain,(
% 0.21/0.49    $false | spl3_20),
% 0.21/0.49    inference(subsumption_resolution,[],[f559,f136])).
% 0.21/0.49  fof(f559,plain,(
% 0.21/0.49    ~v1_relat_1(sK2) | spl3_20),
% 0.21/0.49    inference(subsumption_resolution,[],[f558,f47])).
% 0.21/0.49  fof(f558,plain,(
% 0.21/0.49    ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_20),
% 0.21/0.49    inference(subsumption_resolution,[],[f557,f43])).
% 0.21/0.49  fof(f557,plain,(
% 0.21/0.49    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_20),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f556])).
% 0.21/0.50  fof(f556,plain,(
% 0.21/0.50    k1_relat_1(sK2) != k1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_20),
% 0.21/0.50    inference(superposition,[],[f554,f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.50  fof(f554,plain,(
% 0.21/0.50    k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | spl3_20),
% 0.21/0.50    inference(avatar_component_clause,[],[f552])).
% 0.21/0.50  fof(f555,plain,(
% 0.21/0.50    ~spl3_19 | ~spl3_20 | ~spl3_2 | ~spl3_4 | spl3_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f546,f190,f128,f112,f552,f548])).
% 0.21/0.50  fof(f190,plain,(
% 0.21/0.50    spl3_8 <=> u1_struct_0(sK0) = k2_relset_1(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.50  fof(f546,plain,(
% 0.21/0.50    k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | (~spl3_2 | ~spl3_4 | spl3_8)),
% 0.21/0.50    inference(superposition,[],[f544,f67])).
% 0.21/0.50  fof(f544,plain,(
% 0.21/0.50    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_2 | ~spl3_4 | spl3_8)),
% 0.21/0.50    inference(subsumption_resolution,[],[f543,f43])).
% 0.21/0.50  fof(f543,plain,(
% 0.21/0.50    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_2 | ~spl3_4 | spl3_8)),
% 0.21/0.50    inference(subsumption_resolution,[],[f542,f47])).
% 0.21/0.50  fof(f542,plain,(
% 0.21/0.50    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | (~spl3_2 | ~spl3_4 | spl3_8)),
% 0.21/0.50    inference(subsumption_resolution,[],[f541,f262])).
% 0.21/0.50  fof(f541,plain,(
% 0.21/0.50    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | (~spl3_2 | ~spl3_4 | spl3_8)),
% 0.21/0.50    inference(subsumption_resolution,[],[f540,f261])).
% 0.21/0.50  fof(f540,plain,(
% 0.21/0.50    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | (~spl3_2 | ~spl3_4 | spl3_8)),
% 0.21/0.50    inference(subsumption_resolution,[],[f538,f260])).
% 0.21/0.50  fof(f538,plain,(
% 0.21/0.50    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | (~spl3_2 | ~spl3_4 | spl3_8)),
% 0.21/0.50    inference(superposition,[],[f270,f77])).
% 0.21/0.50  fof(f270,plain,(
% 0.21/0.50    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | (~spl3_2 | ~spl3_4 | spl3_8)),
% 0.21/0.50    inference(backward_demodulation,[],[f192,f259])).
% 0.21/0.50  fof(f192,plain,(
% 0.21/0.50    u1_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)) | spl3_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f190])).
% 0.21/0.50  fof(f385,plain,(
% 0.21/0.50    ~spl3_2 | ~spl3_5),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f384])).
% 0.21/0.50  fof(f384,plain,(
% 0.21/0.50    $false | (~spl3_2 | ~spl3_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f379,f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    v1_xboole_0(k1_xboole_0)),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    v1_xboole_0(k1_xboole_0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.50  fof(f379,plain,(
% 0.21/0.50    ~v1_xboole_0(k1_xboole_0) | (~spl3_2 | ~spl3_5)),
% 0.21/0.50    inference(backward_demodulation,[],[f211,f360])).
% 0.21/0.50  fof(f360,plain,(
% 0.21/0.50    k1_xboole_0 = k2_relat_1(sK2) | (~spl3_2 | ~spl3_5)),
% 0.21/0.50    inference(backward_demodulation,[],[f162,f134])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    k1_xboole_0 = u1_struct_0(sK1) | ~spl3_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f132])).
% 0.21/0.50  fof(f132,plain,(
% 0.21/0.50    spl3_5 <=> k1_xboole_0 = u1_struct_0(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.50  fof(f211,plain,(
% 0.21/0.50    ~v1_xboole_0(k2_relat_1(sK2)) | ~spl3_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f210,f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ~v2_struct_0(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f210,plain,(
% 0.21/0.50    ~v1_xboole_0(k2_relat_1(sK2)) | v2_struct_0(sK1) | ~spl3_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f208,f50])).
% 0.21/0.50  fof(f208,plain,(
% 0.21/0.50    ~v1_xboole_0(k2_relat_1(sK2)) | ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl3_2),
% 0.21/0.50    inference(superposition,[],[f57,f162])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,axiom,(
% 0.21/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.50  % (5459)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  fof(f343,plain,(
% 0.21/0.50    ~spl3_2 | ~spl3_4 | spl3_11),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f342])).
% 0.21/0.50  fof(f342,plain,(
% 0.21/0.50    $false | (~spl3_2 | ~spl3_4 | spl3_11)),
% 0.21/0.50    inference(subsumption_resolution,[],[f341,f136])).
% 0.21/0.50  fof(f341,plain,(
% 0.21/0.50    ~v1_relat_1(sK2) | (~spl3_2 | ~spl3_4 | spl3_11)),
% 0.21/0.50    inference(subsumption_resolution,[],[f340,f47])).
% 0.21/0.50  fof(f340,plain,(
% 0.21/0.50    ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_2 | ~spl3_4 | spl3_11)),
% 0.21/0.50    inference(subsumption_resolution,[],[f339,f43])).
% 0.21/0.50  fof(f339,plain,(
% 0.21/0.50    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_2 | ~spl3_4 | spl3_11)),
% 0.21/0.50    inference(subsumption_resolution,[],[f338,f265])).
% 0.21/0.50  fof(f265,plain,(
% 0.21/0.50    r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | (~spl3_2 | ~spl3_4)),
% 0.21/0.50    inference(backward_demodulation,[],[f167,f259])).
% 0.21/0.50  fof(f167,plain,(
% 0.21/0.50    r2_funct_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2,sK2) | ~spl3_2),
% 0.21/0.50    inference(backward_demodulation,[],[f102,f162])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f101,f43])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    ~v1_funct_1(sK2) | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f93,f44])).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK2)),
% 0.21/0.50    inference(resolution,[],[f45,f85])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X0,X1,X2) | ~v1_funct_1(X0) | r2_funct_2(X1,X2,X0,X0)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f84])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | ~v1_funct_2(X0,X1,X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X0,X1,X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_funct_2(X1,X2,X0,X0)) )),
% 0.21/0.50    inference(condensation,[],[f78])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X2,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.50    inference(flattening,[],[f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).
% 0.21/0.50  fof(f338,plain,(
% 0.21/0.50    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_2 | ~spl3_4 | spl3_11)),
% 0.21/0.50    inference(superposition,[],[f329,f58])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).
% 0.21/0.50  fof(f329,plain,(
% 0.21/0.50    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(k2_funct_1(sK2)),sK2) | (~spl3_2 | ~spl3_4 | spl3_11)),
% 0.21/0.50    inference(subsumption_resolution,[],[f328,f43])).
% 0.21/0.50  fof(f328,plain,(
% 0.21/0.50    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(k2_funct_1(sK2)),sK2) | ~v1_funct_1(sK2) | (~spl3_2 | ~spl3_4 | spl3_11)),
% 0.21/0.50    inference(subsumption_resolution,[],[f327,f47])).
% 0.21/0.50  fof(f327,plain,(
% 0.21/0.50    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(k2_funct_1(sK2)),sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | (~spl3_2 | ~spl3_4 | spl3_11)),
% 0.21/0.50    inference(subsumption_resolution,[],[f326,f262])).
% 0.21/0.50  fof(f326,plain,(
% 0.21/0.50    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(k2_funct_1(sK2)),sK2) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | (~spl3_2 | ~spl3_4 | spl3_11)),
% 0.21/0.50    inference(subsumption_resolution,[],[f325,f261])).
% 0.21/0.50  fof(f325,plain,(
% 0.21/0.50    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(k2_funct_1(sK2)),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | (~spl3_2 | ~spl3_4 | spl3_11)),
% 0.21/0.50    inference(subsumption_resolution,[],[f324,f260])).
% 0.21/0.50  fof(f324,plain,(
% 0.21/0.50    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(k2_funct_1(sK2)),sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | (~spl3_2 | ~spl3_4 | spl3_11)),
% 0.21/0.50    inference(superposition,[],[f273,f77])).
% 0.21/0.50  fof(f273,plain,(
% 0.21/0.50    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2) | (~spl3_2 | ~spl3_4 | spl3_11)),
% 0.21/0.50    inference(backward_demodulation,[],[f204,f259])).
% 0.21/0.50  fof(f204,plain,(
% 0.21/0.50    ~r2_funct_2(u1_struct_0(sK0),k2_relat_1(sK2),k2_funct_1(k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2) | spl3_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f202])).
% 0.21/0.50  fof(f202,plain,(
% 0.21/0.50    spl3_11 <=> r2_funct_2(u1_struct_0(sK0),k2_relat_1(sK2),k2_funct_1(k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.50  fof(f336,plain,(
% 0.21/0.50    ~spl3_2 | ~spl3_4 | spl3_9),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f335])).
% 0.21/0.50  fof(f335,plain,(
% 0.21/0.50    $false | (~spl3_2 | ~spl3_4 | spl3_9)),
% 0.21/0.50    inference(subsumption_resolution,[],[f334,f43])).
% 0.21/0.50  fof(f334,plain,(
% 0.21/0.50    ~v1_funct_1(sK2) | (~spl3_2 | ~spl3_4 | spl3_9)),
% 0.21/0.50    inference(subsumption_resolution,[],[f333,f262])).
% 0.21/0.50  fof(f333,plain,(
% 0.21/0.50    k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_funct_1(sK2) | (~spl3_2 | ~spl3_4 | spl3_9)),
% 0.21/0.50    inference(subsumption_resolution,[],[f332,f47])).
% 0.21/0.50  fof(f332,plain,(
% 0.21/0.50    ~v2_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_funct_1(sK2) | (~spl3_2 | ~spl3_4 | spl3_9)),
% 0.21/0.50    inference(subsumption_resolution,[],[f331,f261])).
% 0.21/0.50  fof(f331,plain,(
% 0.21/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v2_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_funct_1(sK2) | (~spl3_2 | ~spl3_4 | spl3_9)),
% 0.21/0.50    inference(subsumption_resolution,[],[f330,f260])).
% 0.21/0.50  fof(f330,plain,(
% 0.21/0.50    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v2_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_funct_1(sK2) | (~spl3_2 | ~spl3_4 | spl3_9)),
% 0.21/0.50    inference(resolution,[],[f323,f76])).
% 0.21/0.50  fof(f323,plain,(
% 0.21/0.50    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | (~spl3_2 | ~spl3_4 | spl3_9)),
% 0.21/0.50    inference(subsumption_resolution,[],[f322,f43])).
% 0.21/0.50  fof(f322,plain,(
% 0.21/0.50    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_funct_1(sK2) | (~spl3_2 | ~spl3_4 | spl3_9)),
% 0.21/0.50    inference(subsumption_resolution,[],[f321,f47])).
% 0.21/0.50  fof(f321,plain,(
% 0.21/0.50    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | (~spl3_2 | ~spl3_4 | spl3_9)),
% 0.21/0.50    inference(subsumption_resolution,[],[f320,f262])).
% 0.21/0.50  fof(f320,plain,(
% 0.21/0.50    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | (~spl3_2 | ~spl3_4 | spl3_9)),
% 0.21/0.50    inference(subsumption_resolution,[],[f319,f261])).
% 0.21/0.50  fof(f319,plain,(
% 0.21/0.50    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | (~spl3_2 | ~spl3_4 | spl3_9)),
% 0.21/0.50    inference(subsumption_resolution,[],[f318,f260])).
% 0.21/0.50  fof(f318,plain,(
% 0.21/0.50    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | (~spl3_2 | ~spl3_4 | spl3_9)),
% 0.21/0.50    inference(superposition,[],[f271,f77])).
% 0.21/0.50  fof(f271,plain,(
% 0.21/0.50    ~m1_subset_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | (~spl3_2 | ~spl3_4 | spl3_9)),
% 0.21/0.50    inference(backward_demodulation,[],[f196,f259])).
% 0.21/0.50  fof(f196,plain,(
% 0.21/0.50    ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),u1_struct_0(sK0)))) | spl3_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f194])).
% 0.21/0.50  fof(f314,plain,(
% 0.21/0.50    ~spl3_2 | ~spl3_3 | ~spl3_4 | spl3_10),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f313])).
% 0.21/0.50  fof(f313,plain,(
% 0.21/0.50    $false | (~spl3_2 | ~spl3_3 | ~spl3_4 | spl3_10)),
% 0.21/0.50    inference(subsumption_resolution,[],[f312,f43])).
% 0.21/0.50  fof(f312,plain,(
% 0.21/0.50    ~v1_funct_1(sK2) | (~spl3_2 | ~spl3_3 | ~spl3_4 | spl3_10)),
% 0.21/0.50    inference(subsumption_resolution,[],[f311,f47])).
% 0.21/0.50  fof(f311,plain,(
% 0.21/0.50    ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | (~spl3_2 | ~spl3_3 | ~spl3_4 | spl3_10)),
% 0.21/0.50    inference(subsumption_resolution,[],[f310,f262])).
% 0.21/0.50  fof(f310,plain,(
% 0.21/0.50    k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | (~spl3_2 | ~spl3_3 | ~spl3_4 | spl3_10)),
% 0.21/0.50    inference(subsumption_resolution,[],[f309,f261])).
% 0.21/0.50  fof(f309,plain,(
% 0.21/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | (~spl3_2 | ~spl3_3 | ~spl3_4 | spl3_10)),
% 0.21/0.50    inference(subsumption_resolution,[],[f308,f260])).
% 0.21/0.50  fof(f308,plain,(
% 0.21/0.50    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | (~spl3_2 | ~spl3_3 | ~spl3_4 | spl3_10)),
% 0.21/0.50    inference(subsumption_resolution,[],[f307,f263])).
% 0.21/0.50  fof(f263,plain,(
% 0.21/0.50    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | (~spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.21/0.50    inference(backward_demodulation,[],[f161,f259])).
% 0.21/0.50  fof(f161,plain,(
% 0.21/0.50    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),u1_struct_0(sK0)) | ~spl3_3),
% 0.21/0.50    inference(forward_demodulation,[],[f124,f145])).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),u1_struct_0(sK0)) | ~spl3_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f122])).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    spl3_3 <=> v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.50  fof(f307,plain,(
% 0.21/0.50    ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | (~spl3_2 | ~spl3_4 | spl3_10)),
% 0.21/0.50    inference(superposition,[],[f272,f77])).
% 0.21/0.50  fof(f272,plain,(
% 0.21/0.50    ~v1_funct_2(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | (~spl3_2 | ~spl3_4 | spl3_10)),
% 0.21/0.50    inference(backward_demodulation,[],[f200,f259])).
% 0.21/0.50  fof(f200,plain,(
% 0.21/0.50    ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2),k2_relat_1(sK2),u1_struct_0(sK0)) | spl3_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f198])).
% 0.21/0.50  fof(f198,plain,(
% 0.21/0.50    spl3_10 <=> v1_funct_2(k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2),k2_relat_1(sK2),u1_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.50  fof(f226,plain,(
% 0.21/0.50    ~spl3_1 | spl3_6),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f225])).
% 0.21/0.50  fof(f225,plain,(
% 0.21/0.50    $false | (~spl3_1 | spl3_6)),
% 0.21/0.50    inference(subsumption_resolution,[],[f224,f43])).
% 0.21/0.50  fof(f224,plain,(
% 0.21/0.50    ~v1_funct_1(sK2) | (~spl3_1 | spl3_6)),
% 0.21/0.50    inference(subsumption_resolution,[],[f223,f47])).
% 0.21/0.50  fof(f223,plain,(
% 0.21/0.50    ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | (~spl3_1 | spl3_6)),
% 0.21/0.50    inference(subsumption_resolution,[],[f222,f153])).
% 0.21/0.50  fof(f222,plain,(
% 0.21/0.50    k2_relat_1(sK2) != k2_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | (~spl3_1 | spl3_6)),
% 0.21/0.50    inference(subsumption_resolution,[],[f221,f151])).
% 0.21/0.50  fof(f221,plain,(
% 0.21/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2)))) | k2_relat_1(sK2) != k2_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | (~spl3_1 | spl3_6)),
% 0.21/0.50    inference(subsumption_resolution,[],[f220,f147])).
% 0.21/0.50  fof(f220,plain,(
% 0.21/0.50    ~v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2)))) | k2_relat_1(sK2) != k2_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | (~spl3_1 | spl3_6)),
% 0.21/0.50    inference(subsumption_resolution,[],[f218,f110])).
% 0.21/0.50  fof(f218,plain,(
% 0.21/0.50    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2)))) | k2_relat_1(sK2) != k2_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | spl3_6),
% 0.21/0.50    inference(superposition,[],[f184,f77])).
% 0.21/0.50  fof(f184,plain,(
% 0.21/0.50    ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)) | spl3_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f182])).
% 0.21/0.50  fof(f182,plain,(
% 0.21/0.50    spl3_6 <=> v1_funct_1(k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.50  fof(f205,plain,(
% 0.21/0.50    ~spl3_6 | ~spl3_7 | ~spl3_8 | ~spl3_9 | ~spl3_10 | ~spl3_11 | ~spl3_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f174,f112,f202,f198,f194,f190,f186,f182])).
% 0.21/0.50  fof(f174,plain,(
% 0.21/0.50    ~r2_funct_2(u1_struct_0(sK0),k2_relat_1(sK2),k2_funct_1(k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2),k2_relat_1(sK2),u1_struct_0(sK0)) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),u1_struct_0(sK0)))) | u1_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)) | ~v2_funct_1(k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)) | ~spl3_2),
% 0.21/0.50    inference(superposition,[],[f165,f77])).
% 0.21/0.50  fof(f165,plain,(
% 0.21/0.50    ~r2_funct_2(u1_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2) | ~spl3_2),
% 0.21/0.50    inference(backward_demodulation,[],[f48,f162])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f160,plain,(
% 0.21/0.50    spl3_2),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f159])).
% 0.21/0.50  fof(f159,plain,(
% 0.21/0.50    $false | spl3_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f158,f50])).
% 0.21/0.50  fof(f158,plain,(
% 0.21/0.50    ~l1_struct_0(sK1) | spl3_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f157,f145])).
% 0.21/0.50  fof(f157,plain,(
% 0.21/0.50    k2_struct_0(sK1) != k2_relat_1(sK2) | ~l1_struct_0(sK1) | spl3_2),
% 0.21/0.50    inference(superposition,[],[f149,f55])).
% 0.21/0.50  fof(f149,plain,(
% 0.21/0.50    u1_struct_0(sK1) != k2_relat_1(sK2) | spl3_2),
% 0.21/0.50    inference(backward_demodulation,[],[f114,f145])).
% 0.21/0.50  fof(f114,plain,(
% 0.21/0.50    u1_struct_0(sK1) != k2_struct_0(sK1) | spl3_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f112])).
% 0.21/0.50  fof(f135,plain,(
% 0.21/0.50    spl3_4 | spl3_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f126,f132,f128])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    k1_xboole_0 = u1_struct_0(sK1) | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f97,f44])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    k1_xboole_0 = u1_struct_0(sK1) | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.50    inference(resolution,[],[f45,f73])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(flattening,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    spl3_3 | ~spl3_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f120,f112,f122])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    u1_struct_0(sK1) != k2_struct_0(sK1) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.50    inference(inner_rewriting,[],[f119])).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    u1_struct_0(sK1) != k2_struct_0(sK1) | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.50    inference(forward_demodulation,[],[f118,f46])).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.50    inference(subsumption_resolution,[],[f117,f47])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    ~v2_funct_1(sK2) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.50    inference(subsumption_resolution,[],[f116,f43])).
% 0.21/0.50  fof(f116,plain,(
% 0.21/0.50    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.50    inference(subsumption_resolution,[],[f95,f44])).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.50    inference(resolution,[],[f45,f75])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_2(k2_funct_1(X2),X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    spl3_1 | ~spl3_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f106,f112,f108])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    u1_struct_0(sK1) != k2_struct_0(sK1) | v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.50    inference(forward_demodulation,[],[f105,f46])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.50    inference(subsumption_resolution,[],[f104,f47])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    ~v2_funct_1(sK2) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.50    inference(subsumption_resolution,[],[f103,f43])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.50    inference(subsumption_resolution,[],[f94,f44])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.50    inference(resolution,[],[f45,f74])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_1(k2_funct_1(X2))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (5447)------------------------------
% 0.21/0.50  % (5447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (5447)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (5447)Memory used [KB]: 10874
% 0.21/0.50  % (5447)Time elapsed: 0.060 s
% 0.21/0.50  % (5447)------------------------------
% 0.21/0.50  % (5447)------------------------------
% 0.21/0.50  % (5452)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (5445)Success in time 0.14 s
%------------------------------------------------------------------------------
