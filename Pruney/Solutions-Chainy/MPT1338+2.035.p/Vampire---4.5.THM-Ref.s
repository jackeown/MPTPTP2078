%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:05 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :  153 (7909 expanded)
%              Number of leaves         :   19 (1593 expanded)
%              Depth                    :   20
%              Number of atoms          :  430 (41642 expanded)
%              Number of equality atoms :  147 (13621 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f557,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f211,f258,f262,f382,f408,f556])).

fof(f556,plain,
    ( spl7_2
    | spl7_6
    | ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f552])).

fof(f552,plain,
    ( $false
    | spl7_2
    | spl7_6
    | ~ spl7_7 ),
    inference(unit_resulting_resolution,[],[f545,f544])).

fof(f544,plain,
    ( k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_xboole_0,k1_xboole_0)
    | spl7_2
    | spl7_6
    | ~ spl7_7 ),
    inference(backward_demodulation,[],[f494,f521])).

fof(f521,plain,
    ( k1_xboole_0 = k2_funct_1(sK2)
    | spl7_2
    | spl7_6
    | ~ spl7_7 ),
    inference(unit_resulting_resolution,[],[f248,f490,f491,f102])).

fof(f102,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f491,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_xboole_0)))
    | spl7_2
    | ~ spl7_7 ),
    inference(backward_demodulation,[],[f390,f473])).

fof(f473,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | spl7_2
    | ~ spl7_7 ),
    inference(unit_resulting_resolution,[],[f389,f410,f390,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f410,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | spl7_2
    | ~ spl7_7 ),
    inference(forward_demodulation,[],[f409,f391])).

fof(f391,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl7_7 ),
    inference(backward_demodulation,[],[f215,f253])).

fof(f253,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f251])).

fof(f251,plain,
    ( spl7_7
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f215,plain,(
    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f52,f48,f151,f150,f158,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f158,plain,(
    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(backward_demodulation,[],[f141,f147])).

fof(f147,plain,(
    k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f126,f141])).

fof(f126,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f121,f124])).

fof(f124,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f55,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f55,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
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
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
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

fof(f121,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f51,f116])).

fof(f116,plain,(
    k2_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(unit_resulting_resolution,[],[f54,f69])).

fof(f54,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f51,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f141,plain,(
    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(unit_resulting_resolution,[],[f127,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f127,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f120,f124])).

fof(f120,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f50,f116])).

fof(f50,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f27])).

fof(f150,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    inference(backward_demodulation,[],[f127,f147])).

fof(f151,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f128,f147])).

fof(f128,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f119,f124])).

fof(f119,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f49,f116])).

fof(f49,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f48,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f52,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f409,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | spl7_2
    | ~ spl7_7 ),
    inference(forward_demodulation,[],[f210,f253])).

fof(f210,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | spl7_2 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl7_2
  <=> k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f389,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl7_7 ),
    inference(backward_demodulation,[],[f213,f253])).

fof(f213,plain,(
    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f48,f52,f151,f150,f158,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_2(k2_funct_1(X2),X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

% (20798)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f18,axiom,(
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

fof(f390,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl7_7 ),
    inference(backward_demodulation,[],[f214,f253])).

fof(f214,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f48,f52,f151,f150,f158,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f490,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_xboole_0)
    | spl7_2
    | ~ spl7_7 ),
    inference(backward_demodulation,[],[f389,f473])).

fof(f248,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | spl7_6 ),
    inference(avatar_component_clause,[],[f247])).

fof(f247,plain,
    ( spl7_6
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f494,plain,
    ( k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_xboole_0,k2_funct_1(sK2))
    | spl7_2
    | ~ spl7_7 ),
    inference(backward_demodulation,[],[f393,f473])).

fof(f393,plain,
    ( k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl7_7 ),
    inference(backward_demodulation,[],[f226,f253])).

fof(f226,plain,(
    k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f217,f171])).

fof(f171,plain,(
    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f48,f52,f142,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f142,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f127,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f217,plain,(
    k1_relat_1(k2_funct_1(sK2)) = k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f214,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f545,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_xboole_0,k1_xboole_0)
    | spl7_2
    | spl7_6
    | ~ spl7_7 ),
    inference(backward_demodulation,[],[f495,f521])).

fof(f495,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_xboole_0,k2_funct_1(sK2))
    | spl7_2
    | ~ spl7_7 ),
    inference(backward_demodulation,[],[f410,f473])).

fof(f408,plain,
    ( spl7_1
    | ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f404])).

fof(f404,plain,
    ( $false
    | spl7_1
    | ~ spl7_7 ),
    inference(unit_resulting_resolution,[],[f225,f253])).

fof(f225,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | spl7_1 ),
    inference(backward_demodulation,[],[f216,f224])).

fof(f224,plain,(
    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f218,f172])).

fof(f172,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f48,f52,f142,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f218,plain,(
    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f214,f70])).

fof(f216,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | spl7_1 ),
    inference(backward_demodulation,[],[f206,f215])).

fof(f206,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl7_1
  <=> k2_struct_0(sK0) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f382,plain,(
    ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f364])).

fof(f364,plain,
    ( $false
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f86,f318,f359,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ v1_xboole_0(X1)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f359,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl7_6 ),
    inference(superposition,[],[f86,f351])).

fof(f351,plain,
    ( k1_xboole_0 = sK5(k1_xboole_0)
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f87,f271,f77])).

fof(f77,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 != k3_tarski(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( ? [X1] :
            ( r2_hidden(X1,X0)
            & k1_xboole_0 != X1 )
        | k1_xboole_0 = k3_tarski(X0) )
      & ( k1_xboole_0 != k3_tarski(X0)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X2] :
              ( r2_hidden(X2,X0)
              & k1_xboole_0 != X2 ) ) ) ),
    inference(rectify,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X1] :
              ( r2_hidden(X1,X0)
              & k1_xboole_0 != X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_orders_1)).

fof(f271,plain,
    ( r2_hidden(sK5(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f156,f249])).

fof(f249,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f247])).

fof(f156,plain,(
    r2_hidden(sK5(k2_relat_1(sK2)),k1_zfmisc_1(k2_relat_1(sK2))) ),
    inference(backward_demodulation,[],[f138,f147])).

fof(f138,plain,(
    r2_hidden(sK5(k2_struct_0(sK1)),k1_zfmisc_1(k2_struct_0(sK1))) ),
    inference(unit_resulting_resolution,[],[f85,f135,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f135,plain,(
    ~ v1_xboole_0(k1_zfmisc_1(k2_struct_0(sK1))) ),
    inference(unit_resulting_resolution,[],[f114,f123,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f123,plain,(
    m1_subset_1(sK3(sK1),k1_zfmisc_1(k2_struct_0(sK1))) ),
    inference(forward_demodulation,[],[f113,f116])).

fof(f113,plain,(
    m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unit_resulting_resolution,[],[f53,f54,f71])).

fof(f71,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc20_struct_0)).

fof(f53,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f114,plain,(
    ~ v1_xboole_0(sK3(sK1)) ),
    inference(unit_resulting_resolution,[],[f53,f54,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK3(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f85,plain,(
    ! [X0] : m1_subset_1(sK5(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

fof(f87,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f318,plain,
    ( ! [X0] : ~ m1_subset_1(k1_xboole_0,sK5(X0))
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f131,f313])).

fof(f313,plain,
    ( k1_xboole_0 = sK3(sK1)
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f87,f270,f77])).

fof(f270,plain,
    ( r2_hidden(sK3(sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f155,f249])).

fof(f155,plain,(
    r2_hidden(sK3(sK1),k1_zfmisc_1(k2_relat_1(sK2))) ),
    inference(backward_demodulation,[],[f137,f147])).

fof(f137,plain,(
    r2_hidden(sK3(sK1),k1_zfmisc_1(k2_struct_0(sK1))) ),
    inference(unit_resulting_resolution,[],[f123,f135,f84])).

fof(f131,plain,(
    ! [X0] : ~ m1_subset_1(sK3(sK1),sK5(X0)) ),
    inference(unit_resulting_resolution,[],[f86,f114,f82])).

fof(f86,plain,(
    ! [X0] : v1_xboole_0(sK5(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f262,plain,(
    spl7_8 ),
    inference(avatar_contradiction_clause,[],[f259])).

fof(f259,plain,
    ( $false
    | spl7_8 ),
    inference(unit_resulting_resolution,[],[f151,f257])).

fof(f257,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | spl7_8 ),
    inference(avatar_component_clause,[],[f255])).

fof(f255,plain,
    ( spl7_8
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f258,plain,
    ( spl7_6
    | spl7_7
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f170,f255,f251,f247])).

fof(f170,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f169,f147])).

fof(f169,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k1_xboole_0 = k2_relat_1(sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f168,f160])).

fof(f160,plain,(
    k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(forward_demodulation,[],[f140,f147])).

fof(f140,plain,(
    k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(unit_resulting_resolution,[],[f127,f62])).

fof(f168,plain,
    ( k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | k1_xboole_0 = k2_relat_1(sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f167,f147])).

fof(f167,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f146,f147])).

fof(f146,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(resolution,[],[f127,f61])).

fof(f211,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f159,f208,f204])).

fof(f159,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) ),
    inference(forward_demodulation,[],[f152,f147])).

fof(f152,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(backward_demodulation,[],[f130,f147])).

fof(f130,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(forward_demodulation,[],[f129,f124])).

fof(f129,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(backward_demodulation,[],[f122,f124])).

fof(f122,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(forward_demodulation,[],[f118,f116])).

fof(f118,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(backward_demodulation,[],[f47,f116])).

fof(f47,plain,
    ( k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n004.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:35:08 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (20800)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.52  % (20777)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.20/0.52  % (20792)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.20/0.52  % (20782)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.20/0.53  % (20781)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.20/0.53  % (20780)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.20/0.53  % (20776)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.20/0.53  % (20793)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.31/0.53  % (20778)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.31/0.54  % (20773)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.31/0.54  % (20784)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.31/0.54  % (20785)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.31/0.54  % (20774)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.31/0.54  % (20775)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.31/0.55  % (20772)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.31/0.55  % (20801)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.31/0.55  % (20795)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.31/0.55  % (20782)Refutation not found, incomplete strategy% (20782)------------------------------
% 1.31/0.55  % (20782)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (20782)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.55  
% 1.31/0.55  % (20782)Memory used [KB]: 10746
% 1.31/0.55  % (20782)Time elapsed: 0.136 s
% 1.31/0.55  % (20782)------------------------------
% 1.31/0.55  % (20782)------------------------------
% 1.31/0.55  % (20789)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.31/0.55  % (20796)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.31/0.55  % (20794)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.31/0.55  % (20791)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.31/0.55  % (20797)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.31/0.55  % (20776)Refutation found. Thanks to Tanya!
% 1.31/0.55  % SZS status Theorem for theBenchmark
% 1.31/0.55  % SZS output start Proof for theBenchmark
% 1.31/0.55  fof(f557,plain,(
% 1.31/0.55    $false),
% 1.31/0.55    inference(avatar_sat_refutation,[],[f211,f258,f262,f382,f408,f556])).
% 1.31/0.55  fof(f556,plain,(
% 1.31/0.55    spl7_2 | spl7_6 | ~spl7_7),
% 1.31/0.55    inference(avatar_contradiction_clause,[],[f552])).
% 1.31/0.55  fof(f552,plain,(
% 1.31/0.55    $false | (spl7_2 | spl7_6 | ~spl7_7)),
% 1.31/0.55    inference(unit_resulting_resolution,[],[f545,f544])).
% 1.31/0.55  fof(f544,plain,(
% 1.31/0.55    k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_xboole_0,k1_xboole_0) | (spl7_2 | spl7_6 | ~spl7_7)),
% 1.31/0.55    inference(backward_demodulation,[],[f494,f521])).
% 1.31/0.55  fof(f521,plain,(
% 1.31/0.55    k1_xboole_0 = k2_funct_1(sK2) | (spl7_2 | spl7_6 | ~spl7_7)),
% 1.31/0.55    inference(unit_resulting_resolution,[],[f248,f490,f491,f102])).
% 1.31/0.55  fof(f102,plain,(
% 1.31/0.55    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0)) )),
% 1.31/0.55    inference(equality_resolution,[],[f57])).
% 1.31/0.55  fof(f57,plain,(
% 1.31/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 1.31/0.55    inference(cnf_transformation,[],[f29])).
% 1.31/0.55  fof(f29,plain,(
% 1.31/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.31/0.55    inference(flattening,[],[f28])).
% 1.31/0.55  fof(f28,plain,(
% 1.31/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.31/0.55    inference(ennf_transformation,[],[f17])).
% 1.31/0.55  fof(f17,axiom,(
% 1.31/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.31/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.31/0.55  fof(f491,plain,(
% 1.31/0.55    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_xboole_0))) | (spl7_2 | ~spl7_7)),
% 1.31/0.55    inference(backward_demodulation,[],[f390,f473])).
% 1.31/0.55  fof(f473,plain,(
% 1.31/0.55    k1_xboole_0 = k1_relat_1(sK2) | (spl7_2 | ~spl7_7)),
% 1.31/0.55    inference(unit_resulting_resolution,[],[f389,f410,f390,f61])).
% 1.31/0.55  fof(f61,plain,(
% 1.31/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.31/0.55    inference(cnf_transformation,[],[f29])).
% 1.31/0.55  fof(f410,plain,(
% 1.31/0.55    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (spl7_2 | ~spl7_7)),
% 1.31/0.55    inference(forward_demodulation,[],[f409,f391])).
% 1.31/0.55  fof(f391,plain,(
% 1.31/0.55    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl7_7),
% 1.31/0.55    inference(backward_demodulation,[],[f215,f253])).
% 1.31/0.55  fof(f253,plain,(
% 1.31/0.55    k2_struct_0(sK0) = k1_relat_1(sK2) | ~spl7_7),
% 1.31/0.55    inference(avatar_component_clause,[],[f251])).
% 1.31/0.55  fof(f251,plain,(
% 1.31/0.55    spl7_7 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 1.31/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.31/0.55  fof(f215,plain,(
% 1.31/0.55    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 1.31/0.55    inference(unit_resulting_resolution,[],[f52,f48,f151,f150,f158,f63])).
% 1.31/0.55  fof(f63,plain,(
% 1.31/0.55    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)) )),
% 1.31/0.55    inference(cnf_transformation,[],[f32])).
% 1.31/0.55  fof(f32,plain,(
% 1.31/0.55    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.31/0.55    inference(flattening,[],[f31])).
% 1.31/0.55  fof(f31,plain,(
% 1.31/0.55    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.31/0.55    inference(ennf_transformation,[],[f22])).
% 1.31/0.55  fof(f22,axiom,(
% 1.31/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 1.31/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 1.31/0.55  fof(f158,plain,(
% 1.31/0.55    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 1.31/0.55    inference(backward_demodulation,[],[f141,f147])).
% 1.31/0.55  fof(f147,plain,(
% 1.31/0.55    k2_struct_0(sK1) = k2_relat_1(sK2)),
% 1.31/0.55    inference(backward_demodulation,[],[f126,f141])).
% 1.31/0.55  fof(f126,plain,(
% 1.31/0.55    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.31/0.55    inference(backward_demodulation,[],[f121,f124])).
% 1.31/0.55  fof(f124,plain,(
% 1.31/0.55    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.31/0.55    inference(unit_resulting_resolution,[],[f55,f69])).
% 1.31/0.55  fof(f69,plain,(
% 1.31/0.55    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.31/0.55    inference(cnf_transformation,[],[f37])).
% 1.31/0.55  fof(f37,plain,(
% 1.31/0.55    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.31/0.55    inference(ennf_transformation,[],[f19])).
% 1.31/0.55  fof(f19,axiom,(
% 1.31/0.55    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.31/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 1.31/0.55  fof(f55,plain,(
% 1.31/0.55    l1_struct_0(sK0)),
% 1.31/0.55    inference(cnf_transformation,[],[f27])).
% 1.31/0.55  fof(f27,plain,(
% 1.31/0.55    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 1.31/0.55    inference(flattening,[],[f26])).
% 1.31/0.55  fof(f26,plain,(
% 1.31/0.55    ? [X0] : (? [X1] : (? [X2] : (((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 1.31/0.56    inference(ennf_transformation,[],[f24])).
% 1.31/0.56  fof(f24,negated_conjecture,(
% 1.31/0.56    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 1.31/0.56    inference(negated_conjecture,[],[f23])).
% 1.31/0.56  fof(f23,conjecture,(
% 1.31/0.56    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 1.31/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).
% 1.31/0.56  fof(f121,plain,(
% 1.31/0.56    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.31/0.56    inference(backward_demodulation,[],[f51,f116])).
% 1.31/0.56  fof(f116,plain,(
% 1.31/0.56    k2_struct_0(sK1) = u1_struct_0(sK1)),
% 1.31/0.56    inference(unit_resulting_resolution,[],[f54,f69])).
% 1.31/0.56  fof(f54,plain,(
% 1.31/0.56    l1_struct_0(sK1)),
% 1.31/0.56    inference(cnf_transformation,[],[f27])).
% 1.31/0.56  fof(f51,plain,(
% 1.31/0.56    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 1.31/0.56    inference(cnf_transformation,[],[f27])).
% 1.31/0.56  fof(f141,plain,(
% 1.31/0.56    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.31/0.56    inference(unit_resulting_resolution,[],[f127,f70])).
% 1.31/0.56  fof(f70,plain,(
% 1.31/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.31/0.56    inference(cnf_transformation,[],[f38])).
% 1.31/0.56  fof(f38,plain,(
% 1.31/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.31/0.56    inference(ennf_transformation,[],[f16])).
% 1.31/0.56  fof(f16,axiom,(
% 1.31/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.31/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.31/0.56  fof(f127,plain,(
% 1.31/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 1.31/0.56    inference(backward_demodulation,[],[f120,f124])).
% 1.31/0.56  fof(f120,plain,(
% 1.31/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))),
% 1.31/0.56    inference(backward_demodulation,[],[f50,f116])).
% 1.31/0.56  fof(f50,plain,(
% 1.31/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.31/0.56    inference(cnf_transformation,[],[f27])).
% 1.31/0.56  fof(f150,plain,(
% 1.31/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 1.31/0.56    inference(backward_demodulation,[],[f127,f147])).
% 1.31/0.56  fof(f151,plain,(
% 1.31/0.56    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 1.31/0.56    inference(backward_demodulation,[],[f128,f147])).
% 1.31/0.56  fof(f128,plain,(
% 1.31/0.56    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 1.31/0.56    inference(backward_demodulation,[],[f119,f124])).
% 1.31/0.56  fof(f119,plain,(
% 1.31/0.56    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))),
% 1.31/0.56    inference(backward_demodulation,[],[f49,f116])).
% 1.31/0.56  fof(f49,plain,(
% 1.31/0.56    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.31/0.56    inference(cnf_transformation,[],[f27])).
% 1.31/0.56  fof(f48,plain,(
% 1.31/0.56    v1_funct_1(sK2)),
% 1.31/0.56    inference(cnf_transformation,[],[f27])).
% 1.31/0.56  fof(f52,plain,(
% 1.31/0.56    v2_funct_1(sK2)),
% 1.31/0.56    inference(cnf_transformation,[],[f27])).
% 1.31/0.56  fof(f409,plain,(
% 1.31/0.56    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | (spl7_2 | ~spl7_7)),
% 1.31/0.56    inference(forward_demodulation,[],[f210,f253])).
% 1.31/0.56  fof(f210,plain,(
% 1.31/0.56    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | spl7_2),
% 1.31/0.56    inference(avatar_component_clause,[],[f208])).
% 1.31/0.56  fof(f208,plain,(
% 1.31/0.56    spl7_2 <=> k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))),
% 1.31/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.31/0.56  fof(f389,plain,(
% 1.31/0.56    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~spl7_7),
% 1.31/0.56    inference(backward_demodulation,[],[f213,f253])).
% 1.31/0.56  fof(f213,plain,(
% 1.31/0.56    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))),
% 1.31/0.56    inference(unit_resulting_resolution,[],[f48,f52,f151,f150,f158,f65])).
% 1.31/0.56  fof(f65,plain,(
% 1.31/0.56    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_2(k2_funct_1(X2),X1,X0)) )),
% 1.31/0.56    inference(cnf_transformation,[],[f34])).
% 1.31/0.56  fof(f34,plain,(
% 1.31/0.56    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.31/0.56    inference(flattening,[],[f33])).
% 1.31/0.56  fof(f33,plain,(
% 1.31/0.56    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.31/0.56    inference(ennf_transformation,[],[f18])).
% 1.31/0.56  % (20798)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.31/0.56  fof(f18,axiom,(
% 1.31/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.31/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 1.31/0.56  fof(f390,plain,(
% 1.31/0.56    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~spl7_7),
% 1.31/0.56    inference(backward_demodulation,[],[f214,f253])).
% 1.31/0.56  fof(f214,plain,(
% 1.31/0.56    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))),
% 1.31/0.56    inference(unit_resulting_resolution,[],[f48,f52,f151,f150,f158,f66])).
% 1.31/0.56  fof(f66,plain,(
% 1.31/0.56    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 1.31/0.56    inference(cnf_transformation,[],[f34])).
% 1.31/0.56  fof(f490,plain,(
% 1.31/0.56    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_xboole_0) | (spl7_2 | ~spl7_7)),
% 1.31/0.56    inference(backward_demodulation,[],[f389,f473])).
% 1.31/0.56  fof(f248,plain,(
% 1.31/0.56    k1_xboole_0 != k2_relat_1(sK2) | spl7_6),
% 1.31/0.56    inference(avatar_component_clause,[],[f247])).
% 1.31/0.56  fof(f247,plain,(
% 1.31/0.56    spl7_6 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 1.31/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.31/0.56  fof(f494,plain,(
% 1.31/0.56    k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_xboole_0,k2_funct_1(sK2)) | (spl7_2 | ~spl7_7)),
% 1.31/0.56    inference(backward_demodulation,[],[f393,f473])).
% 1.31/0.56  fof(f393,plain,(
% 1.31/0.56    k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl7_7),
% 1.31/0.56    inference(backward_demodulation,[],[f226,f253])).
% 1.31/0.56  fof(f226,plain,(
% 1.31/0.56    k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))),
% 1.31/0.56    inference(forward_demodulation,[],[f217,f171])).
% 1.31/0.56  fof(f171,plain,(
% 1.31/0.56    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 1.31/0.56    inference(unit_resulting_resolution,[],[f48,f52,f142,f67])).
% 1.31/0.56  fof(f67,plain,(
% 1.31/0.56    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 1.31/0.56    inference(cnf_transformation,[],[f36])).
% 1.31/0.56  fof(f36,plain,(
% 1.31/0.56    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.31/0.56    inference(flattening,[],[f35])).
% 1.31/0.56  fof(f35,plain,(
% 1.31/0.56    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.31/0.56    inference(ennf_transformation,[],[f13])).
% 1.31/0.56  fof(f13,axiom,(
% 1.31/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.31/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 1.31/0.56  fof(f142,plain,(
% 1.31/0.56    v1_relat_1(sK2)),
% 1.31/0.56    inference(unit_resulting_resolution,[],[f127,f79])).
% 1.31/0.56  fof(f79,plain,(
% 1.31/0.56    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.31/0.56    inference(cnf_transformation,[],[f43])).
% 1.31/0.56  fof(f43,plain,(
% 1.31/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.31/0.56    inference(ennf_transformation,[],[f14])).
% 1.31/0.56  fof(f14,axiom,(
% 1.31/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.31/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.31/0.56  fof(f217,plain,(
% 1.31/0.56    k1_relat_1(k2_funct_1(sK2)) = k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))),
% 1.31/0.56    inference(unit_resulting_resolution,[],[f214,f62])).
% 1.31/0.56  fof(f62,plain,(
% 1.31/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.31/0.56    inference(cnf_transformation,[],[f30])).
% 1.31/0.56  fof(f30,plain,(
% 1.31/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.31/0.56    inference(ennf_transformation,[],[f15])).
% 1.31/0.56  fof(f15,axiom,(
% 1.31/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.31/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.31/0.56  fof(f545,plain,(
% 1.31/0.56    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_xboole_0,k1_xboole_0) | (spl7_2 | spl7_6 | ~spl7_7)),
% 1.31/0.56    inference(backward_demodulation,[],[f495,f521])).
% 1.31/0.56  fof(f495,plain,(
% 1.31/0.56    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_xboole_0,k2_funct_1(sK2)) | (spl7_2 | ~spl7_7)),
% 1.31/0.56    inference(backward_demodulation,[],[f410,f473])).
% 1.31/0.56  fof(f408,plain,(
% 1.31/0.56    spl7_1 | ~spl7_7),
% 1.31/0.56    inference(avatar_contradiction_clause,[],[f404])).
% 1.31/0.56  fof(f404,plain,(
% 1.31/0.56    $false | (spl7_1 | ~spl7_7)),
% 1.31/0.56    inference(unit_resulting_resolution,[],[f225,f253])).
% 1.31/0.56  fof(f225,plain,(
% 1.31/0.56    k2_struct_0(sK0) != k1_relat_1(sK2) | spl7_1),
% 1.31/0.56    inference(backward_demodulation,[],[f216,f224])).
% 1.31/0.56  fof(f224,plain,(
% 1.31/0.56    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))),
% 1.31/0.56    inference(forward_demodulation,[],[f218,f172])).
% 1.31/0.56  fof(f172,plain,(
% 1.31/0.56    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.31/0.56    inference(unit_resulting_resolution,[],[f48,f52,f142,f68])).
% 1.31/0.56  fof(f68,plain,(
% 1.31/0.56    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 1.31/0.56    inference(cnf_transformation,[],[f36])).
% 1.31/0.56  fof(f218,plain,(
% 1.31/0.56    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))),
% 1.31/0.56    inference(unit_resulting_resolution,[],[f214,f70])).
% 1.31/0.56  fof(f216,plain,(
% 1.31/0.56    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | spl7_1),
% 1.31/0.56    inference(backward_demodulation,[],[f206,f215])).
% 1.31/0.56  fof(f206,plain,(
% 1.31/0.56    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | spl7_1),
% 1.31/0.56    inference(avatar_component_clause,[],[f204])).
% 1.31/0.56  fof(f204,plain,(
% 1.31/0.56    spl7_1 <=> k2_struct_0(sK0) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))),
% 1.31/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.31/0.56  fof(f382,plain,(
% 1.31/0.56    ~spl7_6),
% 1.31/0.56    inference(avatar_contradiction_clause,[],[f364])).
% 1.31/0.56  fof(f364,plain,(
% 1.31/0.56    $false | ~spl7_6),
% 1.31/0.56    inference(unit_resulting_resolution,[],[f86,f318,f359,f81])).
% 1.31/0.56  fof(f81,plain,(
% 1.31/0.56    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~v1_xboole_0(X1) | m1_subset_1(X1,X0)) )),
% 1.31/0.56    inference(cnf_transformation,[],[f45])).
% 1.31/0.56  fof(f45,plain,(
% 1.31/0.56    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.31/0.56    inference(ennf_transformation,[],[f4])).
% 1.31/0.56  fof(f4,axiom,(
% 1.31/0.56    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.31/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.31/0.56  fof(f359,plain,(
% 1.31/0.56    v1_xboole_0(k1_xboole_0) | ~spl7_6),
% 1.31/0.56    inference(superposition,[],[f86,f351])).
% 1.31/0.56  fof(f351,plain,(
% 1.31/0.56    k1_xboole_0 = sK5(k1_xboole_0) | ~spl7_6),
% 1.31/0.56    inference(unit_resulting_resolution,[],[f87,f271,f77])).
% 1.31/0.56  fof(f77,plain,(
% 1.31/0.56    ( ! [X2,X0] : (k1_xboole_0 != k3_tarski(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X2) )),
% 1.31/0.56    inference(cnf_transformation,[],[f42])).
% 1.31/0.56  fof(f42,plain,(
% 1.31/0.56    ! [X0] : ((? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 1.31/0.56    inference(ennf_transformation,[],[f25])).
% 1.31/0.56  fof(f25,plain,(
% 1.31/0.56    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X2] : (r2_hidden(X2,X0) & k1_xboole_0 != X2)))),
% 1.31/0.56    inference(rectify,[],[f21])).
% 1.31/0.56  fof(f21,axiom,(
% 1.31/0.56    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1)))),
% 1.31/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_orders_1)).
% 1.31/0.56  fof(f271,plain,(
% 1.31/0.56    r2_hidden(sK5(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~spl7_6),
% 1.31/0.56    inference(backward_demodulation,[],[f156,f249])).
% 1.31/0.56  fof(f249,plain,(
% 1.31/0.56    k1_xboole_0 = k2_relat_1(sK2) | ~spl7_6),
% 1.31/0.56    inference(avatar_component_clause,[],[f247])).
% 1.31/0.56  fof(f156,plain,(
% 1.31/0.56    r2_hidden(sK5(k2_relat_1(sK2)),k1_zfmisc_1(k2_relat_1(sK2)))),
% 1.31/0.56    inference(backward_demodulation,[],[f138,f147])).
% 1.31/0.56  fof(f138,plain,(
% 1.31/0.56    r2_hidden(sK5(k2_struct_0(sK1)),k1_zfmisc_1(k2_struct_0(sK1)))),
% 1.31/0.56    inference(unit_resulting_resolution,[],[f85,f135,f84])).
% 1.31/0.56  fof(f84,plain,(
% 1.31/0.56    ( ! [X0,X1] : (r2_hidden(X1,X0) | v1_xboole_0(X0) | ~m1_subset_1(X1,X0)) )),
% 1.31/0.56    inference(cnf_transformation,[],[f45])).
% 1.31/0.56  fof(f135,plain,(
% 1.31/0.56    ~v1_xboole_0(k1_zfmisc_1(k2_struct_0(sK1)))),
% 1.31/0.56    inference(unit_resulting_resolution,[],[f114,f123,f82])).
% 1.31/0.56  fof(f82,plain,(
% 1.31/0.56    ( ! [X0,X1] : (~v1_xboole_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,X0)) )),
% 1.31/0.56    inference(cnf_transformation,[],[f45])).
% 1.31/0.56  fof(f123,plain,(
% 1.31/0.56    m1_subset_1(sK3(sK1),k1_zfmisc_1(k2_struct_0(sK1)))),
% 1.31/0.56    inference(forward_demodulation,[],[f113,f116])).
% 1.31/0.56  fof(f113,plain,(
% 1.31/0.56    m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.31/0.56    inference(unit_resulting_resolution,[],[f53,f54,f71])).
% 1.31/0.56  fof(f71,plain,(
% 1.31/0.56    ( ! [X0] : (m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.31/0.56    inference(cnf_transformation,[],[f40])).
% 1.31/0.56  fof(f40,plain,(
% 1.31/0.56    ! [X0] : (? [X1] : (v1_zfmisc_1(X1) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.31/0.56    inference(flattening,[],[f39])).
% 1.31/0.56  fof(f39,plain,(
% 1.31/0.56    ! [X0] : (? [X1] : (v1_zfmisc_1(X1) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.31/0.56    inference(ennf_transformation,[],[f20])).
% 1.31/0.56  fof(f20,axiom,(
% 1.31/0.56    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ? [X1] : (v1_zfmisc_1(X1) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.31/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc20_struct_0)).
% 1.31/0.56  fof(f53,plain,(
% 1.31/0.56    ~v2_struct_0(sK1)),
% 1.31/0.56    inference(cnf_transformation,[],[f27])).
% 1.31/0.56  fof(f114,plain,(
% 1.31/0.56    ~v1_xboole_0(sK3(sK1))),
% 1.31/0.56    inference(unit_resulting_resolution,[],[f53,f54,f72])).
% 1.31/0.56  fof(f72,plain,(
% 1.31/0.56    ( ! [X0] : (~v1_xboole_0(sK3(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.31/0.56    inference(cnf_transformation,[],[f40])).
% 1.31/0.56  fof(f85,plain,(
% 1.31/0.56    ( ! [X0] : (m1_subset_1(sK5(X0),k1_zfmisc_1(X0))) )),
% 1.31/0.56    inference(cnf_transformation,[],[f9])).
% 1.31/0.56  fof(f9,axiom,(
% 1.31/0.56    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.31/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).
% 1.31/0.56  fof(f87,plain,(
% 1.31/0.56    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 1.31/0.56    inference(cnf_transformation,[],[f3])).
% 1.31/0.56  fof(f3,axiom,(
% 1.31/0.56    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 1.31/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 1.31/0.56  fof(f318,plain,(
% 1.31/0.56    ( ! [X0] : (~m1_subset_1(k1_xboole_0,sK5(X0))) ) | ~spl7_6),
% 1.31/0.56    inference(backward_demodulation,[],[f131,f313])).
% 1.31/0.56  fof(f313,plain,(
% 1.31/0.56    k1_xboole_0 = sK3(sK1) | ~spl7_6),
% 1.31/0.56    inference(unit_resulting_resolution,[],[f87,f270,f77])).
% 1.31/0.56  fof(f270,plain,(
% 1.31/0.56    r2_hidden(sK3(sK1),k1_zfmisc_1(k1_xboole_0)) | ~spl7_6),
% 1.31/0.56    inference(backward_demodulation,[],[f155,f249])).
% 1.31/0.56  fof(f155,plain,(
% 1.31/0.56    r2_hidden(sK3(sK1),k1_zfmisc_1(k2_relat_1(sK2)))),
% 1.31/0.56    inference(backward_demodulation,[],[f137,f147])).
% 1.31/0.56  fof(f137,plain,(
% 1.31/0.56    r2_hidden(sK3(sK1),k1_zfmisc_1(k2_struct_0(sK1)))),
% 1.31/0.56    inference(unit_resulting_resolution,[],[f123,f135,f84])).
% 1.31/0.56  fof(f131,plain,(
% 1.31/0.56    ( ! [X0] : (~m1_subset_1(sK3(sK1),sK5(X0))) )),
% 1.31/0.56    inference(unit_resulting_resolution,[],[f86,f114,f82])).
% 1.31/0.56  fof(f86,plain,(
% 1.31/0.56    ( ! [X0] : (v1_xboole_0(sK5(X0))) )),
% 1.31/0.56    inference(cnf_transformation,[],[f9])).
% 1.31/0.56  fof(f262,plain,(
% 1.31/0.56    spl7_8),
% 1.31/0.56    inference(avatar_contradiction_clause,[],[f259])).
% 1.31/0.56  fof(f259,plain,(
% 1.31/0.56    $false | spl7_8),
% 1.31/0.56    inference(unit_resulting_resolution,[],[f151,f257])).
% 1.31/0.56  fof(f257,plain,(
% 1.31/0.56    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | spl7_8),
% 1.31/0.56    inference(avatar_component_clause,[],[f255])).
% 1.31/0.56  fof(f255,plain,(
% 1.31/0.56    spl7_8 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 1.31/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.31/0.56  fof(f258,plain,(
% 1.31/0.56    spl7_6 | spl7_7 | ~spl7_8),
% 1.31/0.56    inference(avatar_split_clause,[],[f170,f255,f251,f247])).
% 1.31/0.56  fof(f170,plain,(
% 1.31/0.56    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | k2_struct_0(sK0) = k1_relat_1(sK2) | k1_xboole_0 = k2_relat_1(sK2)),
% 1.31/0.56    inference(forward_demodulation,[],[f169,f147])).
% 1.31/0.56  fof(f169,plain,(
% 1.31/0.56    k2_struct_0(sK0) = k1_relat_1(sK2) | k1_xboole_0 = k2_relat_1(sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 1.31/0.56    inference(forward_demodulation,[],[f168,f160])).
% 1.31/0.56  fof(f160,plain,(
% 1.31/0.56    k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 1.31/0.56    inference(forward_demodulation,[],[f140,f147])).
% 1.31/0.56  fof(f140,plain,(
% 1.31/0.56    k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.31/0.56    inference(unit_resulting_resolution,[],[f127,f62])).
% 1.31/0.56  fof(f168,plain,(
% 1.31/0.56    k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | k1_xboole_0 = k2_relat_1(sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 1.31/0.56    inference(forward_demodulation,[],[f167,f147])).
% 1.31/0.56  fof(f167,plain,(
% 1.31/0.56    k1_xboole_0 = k2_relat_1(sK2) | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 1.31/0.56    inference(forward_demodulation,[],[f146,f147])).
% 1.31/0.56  fof(f146,plain,(
% 1.31/0.56    k1_xboole_0 = k2_struct_0(sK1) | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 1.31/0.56    inference(resolution,[],[f127,f61])).
% 1.31/0.56  fof(f211,plain,(
% 1.31/0.56    ~spl7_1 | ~spl7_2),
% 1.31/0.56    inference(avatar_split_clause,[],[f159,f208,f204])).
% 1.31/0.56  fof(f159,plain,(
% 1.31/0.56    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))),
% 1.31/0.56    inference(forward_demodulation,[],[f152,f147])).
% 1.31/0.56  fof(f152,plain,(
% 1.31/0.56    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 1.31/0.56    inference(backward_demodulation,[],[f130,f147])).
% 1.31/0.56  fof(f130,plain,(
% 1.31/0.56    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 1.31/0.56    inference(forward_demodulation,[],[f129,f124])).
% 1.31/0.56  fof(f129,plain,(
% 1.31/0.56    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 1.31/0.56    inference(backward_demodulation,[],[f122,f124])).
% 1.31/0.56  fof(f122,plain,(
% 1.31/0.56    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 1.31/0.56    inference(forward_demodulation,[],[f118,f116])).
% 1.31/0.56  fof(f118,plain,(
% 1.31/0.56    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 1.31/0.56    inference(backward_demodulation,[],[f47,f116])).
% 1.31/0.56  fof(f47,plain,(
% 1.31/0.56    k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 1.31/0.56    inference(cnf_transformation,[],[f27])).
% 1.31/0.56  % SZS output end Proof for theBenchmark
% 1.31/0.56  % (20776)------------------------------
% 1.31/0.56  % (20776)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.56  % (20776)Termination reason: Refutation
% 1.31/0.56  
% 1.31/0.56  % (20776)Memory used [KB]: 6396
% 1.31/0.56  % (20776)Time elapsed: 0.115 s
% 1.31/0.56  % (20776)------------------------------
% 1.31/0.56  % (20776)------------------------------
% 1.31/0.56  % (20770)Success in time 0.192 s
%------------------------------------------------------------------------------
