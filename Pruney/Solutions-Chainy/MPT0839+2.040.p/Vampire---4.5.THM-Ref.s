%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  140 (1080 expanded)
%              Number of leaves         :   25 ( 330 expanded)
%              Depth                    :   17
%              Number of atoms          :  324 (3114 expanded)
%              Number of equality atoms :   68 ( 513 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f752,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f286,f413,f582,f584,f586,f750])).

fof(f750,plain,(
    ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f740])).

fof(f740,plain,
    ( $false
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f520,f699])).

fof(f699,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f696,f145])).

fof(f145,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f139,f144])).

fof(f144,plain,(
    k1_xboole_0 = k1_relat_1(k1_relat_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f143,f139])).

fof(f143,plain,(
    k1_xboole_0 = k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0))) ),
    inference(forward_demodulation,[],[f119,f139])).

fof(f119,plain,(
    k1_xboole_0 = k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0)))) ),
    inference(unit_resulting_resolution,[],[f48,f75,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f75,plain,(
    v1_xboole_0(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0))))) ),
    inference(unit_resulting_resolution,[],[f70,f50])).

fof(f50,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

fof(f70,plain,(
    v1_xboole_0(k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0)))) ),
    inference(unit_resulting_resolution,[],[f69,f50])).

fof(f69,plain,(
    v1_xboole_0(k1_relat_1(k1_relat_1(k1_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f68,f50])).

fof(f68,plain,(
    v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f48,f50])).

fof(f48,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f139,plain,(
    k1_relat_1(k1_xboole_0) = k1_relat_1(k1_relat_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f134,f138])).

fof(f138,plain,(
    k1_relat_1(k1_xboole_0) = k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0))) ),
    inference(forward_demodulation,[],[f120,f134])).

fof(f120,plain,(
    k1_relat_1(k1_xboole_0) = k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0)))) ),
    inference(unit_resulting_resolution,[],[f68,f75,f59])).

fof(f134,plain,(
    k1_relat_1(k1_relat_1(k1_xboole_0)) = k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0))) ),
    inference(backward_demodulation,[],[f122,f121])).

fof(f121,plain,(
    k1_relat_1(k1_relat_1(k1_xboole_0)) = k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0)))) ),
    inference(unit_resulting_resolution,[],[f69,f75,f59])).

fof(f122,plain,(
    k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0))) = k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0)))) ),
    inference(unit_resulting_resolution,[],[f70,f75,f59])).

fof(f696,plain,
    ( k1_relat_1(k1_xboole_0) = k2_relat_1(sK2)
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f677,f683])).

fof(f683,plain,
    ( k1_xboole_0 = k1_relat_1(k2_relat_1(sK2))
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f664,f677])).

fof(f664,plain,
    ( k1_xboole_0 = k1_relat_1(k1_relat_1(k1_relat_1(k2_relat_1(sK2))))
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f655,f551])).

fof(f551,plain,(
    k2_relat_1(sK2) = k1_relat_1(k3_relset_1(sK1,sK0,sK2)) ),
    inference(forward_demodulation,[],[f530,f511])).

fof(f511,plain,(
    k2_relat_1(sK2) = k1_relset_1(sK0,sK1,k3_relset_1(sK1,sK0,sK2)) ),
    inference(forward_demodulation,[],[f508,f369])).

fof(f369,plain,(
    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f45,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_relset_1(sK1,sK0,sK2))
        | ~ m1_subset_1(X3,sK1) )
    & k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f35,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
                    | ~ m1_subset_1(X3,X1) )
                & k1_xboole_0 != k2_relset_1(X1,X0,X2)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k1_relset_1(X1,sK0,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k2_relset_1(X1,sK0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ! [X3] :
                ( ~ r2_hidden(X3,k1_relset_1(X1,sK0,X2))
                | ~ m1_subset_1(X3,X1) )
            & k1_xboole_0 != k2_relset_1(X1,sK0,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,k1_relset_1(sK1,sK0,X2))
              | ~ m1_subset_1(X3,sK1) )
          & k1_xboole_0 != k2_relset_1(sK1,sK0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X2] :
        ( ! [X3] :
            ( ~ r2_hidden(X3,k1_relset_1(sK1,sK0,X2))
            | ~ m1_subset_1(X3,sK1) )
        & k1_xboole_0 != k2_relset_1(sK1,sK0,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) )
   => ( ! [X3] :
          ( ~ r2_hidden(X3,k1_relset_1(sK1,sK0,sK2))
          | ~ m1_subset_1(X3,sK1) )
      & k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k2_relset_1(X1,X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k2_relset_1(X1,X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,X1)
                       => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
                    & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
                  & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).

fof(f508,plain,(
    k2_relset_1(sK1,sK0,sK2) = k1_relset_1(sK0,sK1,k3_relset_1(sK1,sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f45,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
        & k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
        & k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_relset_1)).

fof(f530,plain,(
    k1_relset_1(sK0,sK1,k3_relset_1(sK1,sK0,sK2)) = k1_relat_1(k3_relset_1(sK1,sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f499,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f499,plain,(
    m1_subset_1(k3_relset_1(sK1,sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f45,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_relset_1)).

fof(f655,plain,
    ( k1_xboole_0 = k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k3_relset_1(sK1,sK0,sK2)))))
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f573,f216])).

fof(f216,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(X0)))) ) ),
    inference(resolution,[],[f202,f50])).

fof(f202,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = k1_relat_1(k1_relat_1(k1_relat_1(X0))) ) ),
    inference(resolution,[],[f199,f50])).

fof(f199,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = k1_relat_1(k1_relat_1(X0)) ) ),
    inference(resolution,[],[f195,f50])).

fof(f195,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = k1_relat_1(X0) ) ),
    inference(resolution,[],[f124,f50])).

fof(f124,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f59,f48])).

fof(f573,plain,
    ( v1_xboole_0(k3_relset_1(sK1,sK0,sK2))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f571])).

fof(f571,plain,
    ( spl4_7
  <=> v1_xboole_0(k3_relset_1(sK1,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f677,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k1_relat_1(k2_relat_1(sK2)))
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f551,f665])).

fof(f665,plain,
    ( k3_relset_1(sK1,sK0,sK2) = k1_relat_1(k2_relat_1(sK2))
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f654,f551])).

fof(f654,plain,
    ( k3_relset_1(sK1,sK0,sK2) = k1_relat_1(k1_relat_1(k3_relset_1(sK1,sK0,sK2)))
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f573,f573,f207])).

fof(f207,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X2)
      | k1_relat_1(k1_relat_1(X2)) = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f125,f50])).

fof(f125,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X2)
      | k1_relat_1(X1) = X2 ) ),
    inference(resolution,[],[f59,f50])).

fof(f520,plain,(
    k1_xboole_0 != k2_relat_1(sK2) ),
    inference(superposition,[],[f46,f369])).

fof(f46,plain,(
    k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f586,plain,(
    spl4_8 ),
    inference(avatar_contradiction_clause,[],[f585])).

fof(f585,plain,
    ( $false
    | spl4_8 ),
    inference(subsumption_resolution,[],[f537,f577])).

fof(f577,plain,
    ( ~ v1_relat_1(k3_relset_1(sK1,sK0,sK2))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f575])).

fof(f575,plain,
    ( spl4_8
  <=> v1_relat_1(k3_relset_1(sK1,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f537,plain,(
    v1_relat_1(k3_relset_1(sK1,sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f54,f499,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f54,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f584,plain,(
    spl4_9 ),
    inference(avatar_contradiction_clause,[],[f583])).

fof(f583,plain,
    ( $false
    | spl4_9 ),
    inference(subsumption_resolution,[],[f48,f581])).

fof(f581,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f579])).

fof(f579,plain,
    ( spl4_9
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f582,plain,
    ( spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f569,f279,f579,f575,f571])).

fof(f279,plain,
    ( spl4_3
  <=> v1_xboole_0(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f569,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k3_relset_1(sK1,sK0,sK2))
    | v1_xboole_0(k3_relset_1(sK1,sK0,sK2))
    | ~ spl4_3 ),
    inference(superposition,[],[f51,f552])).

fof(f552,plain,
    ( k1_xboole_0 = k2_relat_1(k3_relset_1(sK1,sK0,sK2))
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f529,f524])).

fof(f524,plain,
    ( k1_xboole_0 = k2_relset_1(sK0,sK1,k3_relset_1(sK1,sK0,sK2))
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f521,f448])).

fof(f448,plain,
    ( k1_xboole_0 = k1_relset_1(sK1,sK0,sK2)
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f392,f442])).

fof(f442,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f431,f441])).

fof(f441,plain,
    ( k1_xboole_0 = k1_relat_1(k1_relat_1(k1_relat_1(sK2)))
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f432,f431])).

fof(f432,plain,
    ( k1_xboole_0 = k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(sK2)))))
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f281,f216])).

fof(f281,plain,
    ( v1_xboole_0(k1_relat_1(sK2))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f279])).

fof(f431,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k1_relat_1(k1_relat_1(sK2)))
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f281,f281,f207])).

fof(f392,plain,(
    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f45,f61])).

fof(f521,plain,(
    k1_relset_1(sK1,sK0,sK2) = k2_relset_1(sK0,sK1,k3_relset_1(sK1,sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f45,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f529,plain,(
    k2_relset_1(sK0,sK1,k3_relset_1(sK1,sK0,sK2)) = k2_relat_1(k3_relset_1(sK1,sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f499,f60])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

fof(f413,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f412])).

fof(f412,plain,
    ( $false
    | spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f397,f410])).

fof(f410,plain,
    ( ~ r2_hidden(sK3(k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f285,f395])).

fof(f395,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK1)
      | ~ r2_hidden(X3,k1_relat_1(sK2)) ) ),
    inference(backward_demodulation,[],[f47,f392])).

fof(f47,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK1)
      | ~ r2_hidden(X3,k1_relset_1(sK1,sK0,sK2)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f285,plain,
    ( m1_subset_1(sK3(k1_relat_1(sK2)),sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f283])).

fof(f283,plain,
    ( spl4_4
  <=> m1_subset_1(sK3(k1_relat_1(sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f397,plain,
    ( r2_hidden(sK3(k1_relat_1(sK2)),k1_relat_1(sK2))
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f280,f53])).

fof(f53,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f280,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK2))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f279])).

fof(f286,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f277,f283,f279])).

fof(f277,plain,
    ( m1_subset_1(sK3(k1_relat_1(sK2)),sK1)
    | v1_xboole_0(k1_relat_1(sK2)) ),
    inference(resolution,[],[f276,f53])).

fof(f276,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k1_relat_1(sK2))
      | m1_subset_1(X4,sK1) ) ),
    inference(resolution,[],[f67,f245])).

fof(f245,plain,(
    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f242,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f242,plain,(
    r1_tarski(k1_relat_1(sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f188,f239,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f239,plain,(
    v4_relat_1(sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f45,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f188,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f54,f45,f49])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:29:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (10513)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.51  % (10519)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.52  % (10521)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.52  % (10518)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.53  % (10514)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.53  % (10521)Refutation not found, incomplete strategy% (10521)------------------------------
% 0.21/0.53  % (10521)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (10527)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.54  % (10534)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.54  % (10516)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.54  % (10516)Refutation not found, incomplete strategy% (10516)------------------------------
% 0.21/0.54  % (10516)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (10516)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (10516)Memory used [KB]: 10618
% 0.21/0.54  % (10516)Time elapsed: 0.113 s
% 0.21/0.54  % (10516)------------------------------
% 0.21/0.54  % (10516)------------------------------
% 0.21/0.54  % (10524)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.54  % (10536)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.54  % (10521)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (10521)Memory used [KB]: 10618
% 0.21/0.54  % (10521)Time elapsed: 0.103 s
% 0.21/0.54  % (10521)------------------------------
% 0.21/0.54  % (10521)------------------------------
% 0.21/0.55  % (10522)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.55  % (10520)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.56  % (10536)Refutation not found, incomplete strategy% (10536)------------------------------
% 0.21/0.56  % (10536)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (10536)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (10536)Memory used [KB]: 10618
% 0.21/0.56  % (10536)Time elapsed: 0.082 s
% 0.21/0.56  % (10536)------------------------------
% 0.21/0.56  % (10536)------------------------------
% 0.21/0.56  % (10528)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.56  % (10526)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.56  % (10530)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.56  % (10525)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.56  % (10523)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.56  % (10532)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.56  % (10527)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f752,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(avatar_sat_refutation,[],[f286,f413,f582,f584,f586,f750])).
% 0.21/0.56  fof(f750,plain,(
% 0.21/0.56    ~spl4_7),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f740])).
% 0.21/0.56  fof(f740,plain,(
% 0.21/0.56    $false | ~spl4_7),
% 0.21/0.56    inference(subsumption_resolution,[],[f520,f699])).
% 0.21/0.56  fof(f699,plain,(
% 0.21/0.56    k1_xboole_0 = k2_relat_1(sK2) | ~spl4_7),
% 0.21/0.56    inference(forward_demodulation,[],[f696,f145])).
% 0.21/0.56  fof(f145,plain,(
% 0.21/0.56    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.56    inference(backward_demodulation,[],[f139,f144])).
% 0.21/0.56  fof(f144,plain,(
% 0.21/0.56    k1_xboole_0 = k1_relat_1(k1_relat_1(k1_xboole_0))),
% 0.21/0.56    inference(forward_demodulation,[],[f143,f139])).
% 0.21/0.56  fof(f143,plain,(
% 0.21/0.56    k1_xboole_0 = k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0)))),
% 0.21/0.56    inference(forward_demodulation,[],[f119,f139])).
% 0.21/0.56  fof(f119,plain,(
% 0.21/0.56    k1_xboole_0 = k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0))))),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f48,f75,f59])).
% 0.21/0.56  fof(f59,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f25])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 0.21/0.56  fof(f75,plain,(
% 0.21/0.56    v1_xboole_0(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0)))))),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f70,f50])).
% 0.21/0.56  fof(f50,plain,(
% 0.21/0.56    ( ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f21])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,axiom,(
% 0.21/0.56    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).
% 0.21/0.56  fof(f70,plain,(
% 0.21/0.56    v1_xboole_0(k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0))))),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f69,f50])).
% 0.21/0.56  fof(f69,plain,(
% 0.21/0.56    v1_xboole_0(k1_relat_1(k1_relat_1(k1_xboole_0)))),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f68,f50])).
% 0.21/0.56  fof(f68,plain,(
% 0.21/0.56    v1_xboole_0(k1_relat_1(k1_xboole_0))),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f48,f50])).
% 0.21/0.56  fof(f48,plain,(
% 0.21/0.56    v1_xboole_0(k1_xboole_0)),
% 0.21/0.56    inference(cnf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    v1_xboole_0(k1_xboole_0)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.56  fof(f139,plain,(
% 0.21/0.56    k1_relat_1(k1_xboole_0) = k1_relat_1(k1_relat_1(k1_xboole_0))),
% 0.21/0.56    inference(backward_demodulation,[],[f134,f138])).
% 0.21/0.56  fof(f138,plain,(
% 0.21/0.56    k1_relat_1(k1_xboole_0) = k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0)))),
% 0.21/0.56    inference(forward_demodulation,[],[f120,f134])).
% 0.21/0.56  fof(f120,plain,(
% 0.21/0.56    k1_relat_1(k1_xboole_0) = k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0))))),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f68,f75,f59])).
% 0.21/0.56  fof(f134,plain,(
% 0.21/0.56    k1_relat_1(k1_relat_1(k1_xboole_0)) = k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0)))),
% 0.21/0.56    inference(backward_demodulation,[],[f122,f121])).
% 0.21/0.56  fof(f121,plain,(
% 0.21/0.56    k1_relat_1(k1_relat_1(k1_xboole_0)) = k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0))))),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f69,f75,f59])).
% 0.21/0.56  fof(f122,plain,(
% 0.21/0.56    k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0))) = k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0))))),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f70,f75,f59])).
% 0.21/0.56  fof(f696,plain,(
% 0.21/0.56    k1_relat_1(k1_xboole_0) = k2_relat_1(sK2) | ~spl4_7),
% 0.21/0.56    inference(backward_demodulation,[],[f677,f683])).
% 0.21/0.56  fof(f683,plain,(
% 0.21/0.56    k1_xboole_0 = k1_relat_1(k2_relat_1(sK2)) | ~spl4_7),
% 0.21/0.56    inference(backward_demodulation,[],[f664,f677])).
% 0.21/0.56  fof(f664,plain,(
% 0.21/0.56    k1_xboole_0 = k1_relat_1(k1_relat_1(k1_relat_1(k2_relat_1(sK2)))) | ~spl4_7),
% 0.21/0.56    inference(forward_demodulation,[],[f655,f551])).
% 0.21/0.56  fof(f551,plain,(
% 0.21/0.56    k2_relat_1(sK2) = k1_relat_1(k3_relset_1(sK1,sK0,sK2))),
% 0.21/0.56    inference(forward_demodulation,[],[f530,f511])).
% 0.21/0.56  fof(f511,plain,(
% 0.21/0.56    k2_relat_1(sK2) = k1_relset_1(sK0,sK1,k3_relset_1(sK1,sK0,sK2))),
% 0.21/0.56    inference(forward_demodulation,[],[f508,f369])).
% 0.21/0.56  fof(f369,plain,(
% 0.21/0.56    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f45,f60])).
% 0.21/0.56  fof(f60,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f26])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(ennf_transformation,[],[f14])).
% 0.21/0.56  fof(f14,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.56  fof(f45,plain,(
% 0.21/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.56    inference(cnf_transformation,[],[f36])).
% 0.21/0.56  fof(f36,plain,(
% 0.21/0.56    ((! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,sK2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f35,f34,f33])).
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,sK0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,sK0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f34,plain,(
% 0.21/0.56    ? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,sK0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,sK0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))) & ~v1_xboole_0(X1)) => (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,X2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k2_relset_1(sK1,sK0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))) & ~v1_xboole_0(sK1))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f35,plain,(
% 0.21/0.56    ? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,X2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k2_relset_1(sK1,sK0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))) => (! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,sK2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f19,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.56    inference(flattening,[],[f18])).
% 0.21/0.56  fof(f18,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f17])).
% 0.21/0.56  fof(f17,negated_conjecture,(
% 0.21/0.56    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 0.21/0.56    inference(negated_conjecture,[],[f16])).
% 0.21/0.56  fof(f16,conjecture,(
% 0.21/0.56    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).
% 0.21/0.56  fof(f508,plain,(
% 0.21/0.56    k2_relset_1(sK1,sK0,sK2) = k1_relset_1(sK0,sK1,k3_relset_1(sK1,sK0,sK2))),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f45,f65])).
% 0.21/0.56  fof(f65,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f30])).
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) & k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(ennf_transformation,[],[f15])).
% 0.21/0.56  fof(f15,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) & k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_relset_1)).
% 0.21/0.56  fof(f530,plain,(
% 0.21/0.56    k1_relset_1(sK0,sK1,k3_relset_1(sK1,sK0,sK2)) = k1_relat_1(k3_relset_1(sK1,sK0,sK2))),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f499,f61])).
% 0.21/0.56  fof(f61,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f27])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(ennf_transformation,[],[f13])).
% 0.21/0.56  fof(f13,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.56  fof(f499,plain,(
% 0.21/0.56    m1_subset_1(k3_relset_1(sK1,sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f45,f62])).
% 0.21/0.56  fof(f62,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f28])).
% 0.21/0.56  fof(f28,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(ennf_transformation,[],[f12])).
% 0.21/0.56  fof(f12,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_relset_1)).
% 0.21/0.56  fof(f655,plain,(
% 0.21/0.56    k1_xboole_0 = k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k3_relset_1(sK1,sK0,sK2))))) | ~spl4_7),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f573,f216])).
% 0.21/0.56  fof(f216,plain,(
% 0.21/0.56    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(X0))))) )),
% 0.21/0.56    inference(resolution,[],[f202,f50])).
% 0.21/0.56  fof(f202,plain,(
% 0.21/0.56    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = k1_relat_1(k1_relat_1(k1_relat_1(X0)))) )),
% 0.21/0.56    inference(resolution,[],[f199,f50])).
% 0.21/0.56  fof(f199,plain,(
% 0.21/0.56    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = k1_relat_1(k1_relat_1(X0))) )),
% 0.21/0.56    inference(resolution,[],[f195,f50])).
% 0.21/0.56  fof(f195,plain,(
% 0.21/0.56    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = k1_relat_1(X0)) )),
% 0.21/0.56    inference(resolution,[],[f124,f50])).
% 0.21/0.56  fof(f124,plain,(
% 0.21/0.56    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.56    inference(resolution,[],[f59,f48])).
% 0.21/0.56  fof(f573,plain,(
% 0.21/0.56    v1_xboole_0(k3_relset_1(sK1,sK0,sK2)) | ~spl4_7),
% 0.21/0.56    inference(avatar_component_clause,[],[f571])).
% 0.21/0.56  fof(f571,plain,(
% 0.21/0.56    spl4_7 <=> v1_xboole_0(k3_relset_1(sK1,sK0,sK2))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.56  fof(f677,plain,(
% 0.21/0.56    k2_relat_1(sK2) = k1_relat_1(k1_relat_1(k2_relat_1(sK2))) | ~spl4_7),
% 0.21/0.56    inference(backward_demodulation,[],[f551,f665])).
% 0.21/0.56  fof(f665,plain,(
% 0.21/0.56    k3_relset_1(sK1,sK0,sK2) = k1_relat_1(k2_relat_1(sK2)) | ~spl4_7),
% 0.21/0.56    inference(forward_demodulation,[],[f654,f551])).
% 0.21/0.56  fof(f654,plain,(
% 0.21/0.56    k3_relset_1(sK1,sK0,sK2) = k1_relat_1(k1_relat_1(k3_relset_1(sK1,sK0,sK2))) | ~spl4_7),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f573,f573,f207])).
% 0.21/0.56  fof(f207,plain,(
% 0.21/0.56    ( ! [X2,X1] : (~v1_xboole_0(X2) | k1_relat_1(k1_relat_1(X2)) = X1 | ~v1_xboole_0(X1)) )),
% 0.21/0.56    inference(resolution,[],[f125,f50])).
% 0.21/0.56  fof(f125,plain,(
% 0.21/0.56    ( ! [X2,X1] : (~v1_xboole_0(X1) | ~v1_xboole_0(X2) | k1_relat_1(X1) = X2) )),
% 0.21/0.56    inference(resolution,[],[f59,f50])).
% 0.21/0.56  fof(f520,plain,(
% 0.21/0.56    k1_xboole_0 != k2_relat_1(sK2)),
% 0.21/0.56    inference(superposition,[],[f46,f369])).
% 0.21/0.56  fof(f46,plain,(
% 0.21/0.56    k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)),
% 0.21/0.56    inference(cnf_transformation,[],[f36])).
% 0.21/0.56  fof(f586,plain,(
% 0.21/0.56    spl4_8),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f585])).
% 0.21/0.56  fof(f585,plain,(
% 0.21/0.56    $false | spl4_8),
% 0.21/0.56    inference(subsumption_resolution,[],[f537,f577])).
% 0.21/0.56  fof(f577,plain,(
% 0.21/0.56    ~v1_relat_1(k3_relset_1(sK1,sK0,sK2)) | spl4_8),
% 0.21/0.56    inference(avatar_component_clause,[],[f575])).
% 0.21/0.56  fof(f575,plain,(
% 0.21/0.56    spl4_8 <=> v1_relat_1(k3_relset_1(sK1,sK0,sK2))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.56  fof(f537,plain,(
% 0.21/0.56    v1_relat_1(k3_relset_1(sK1,sK0,sK2))),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f54,f499,f49])).
% 0.21/0.56  fof(f49,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f20])).
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.56  fof(f54,plain,(
% 0.21/0.56    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f9])).
% 0.21/0.56  fof(f9,axiom,(
% 0.21/0.56    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.56  fof(f584,plain,(
% 0.21/0.56    spl4_9),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f583])).
% 0.21/0.56  fof(f583,plain,(
% 0.21/0.56    $false | spl4_9),
% 0.21/0.56    inference(subsumption_resolution,[],[f48,f581])).
% 0.21/0.56  fof(f581,plain,(
% 0.21/0.56    ~v1_xboole_0(k1_xboole_0) | spl4_9),
% 0.21/0.56    inference(avatar_component_clause,[],[f579])).
% 0.21/0.56  fof(f579,plain,(
% 0.21/0.56    spl4_9 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.56  fof(f582,plain,(
% 0.21/0.56    spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_3),
% 0.21/0.56    inference(avatar_split_clause,[],[f569,f279,f579,f575,f571])).
% 0.21/0.56  fof(f279,plain,(
% 0.21/0.56    spl4_3 <=> v1_xboole_0(k1_relat_1(sK2))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.56  fof(f569,plain,(
% 0.21/0.56    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k3_relset_1(sK1,sK0,sK2)) | v1_xboole_0(k3_relset_1(sK1,sK0,sK2)) | ~spl4_3),
% 0.21/0.56    inference(superposition,[],[f51,f552])).
% 0.21/0.56  fof(f552,plain,(
% 0.21/0.56    k1_xboole_0 = k2_relat_1(k3_relset_1(sK1,sK0,sK2)) | ~spl4_3),
% 0.21/0.56    inference(forward_demodulation,[],[f529,f524])).
% 0.21/0.56  fof(f524,plain,(
% 0.21/0.56    k1_xboole_0 = k2_relset_1(sK0,sK1,k3_relset_1(sK1,sK0,sK2)) | ~spl4_3),
% 0.21/0.56    inference(forward_demodulation,[],[f521,f448])).
% 0.21/0.56  fof(f448,plain,(
% 0.21/0.56    k1_xboole_0 = k1_relset_1(sK1,sK0,sK2) | ~spl4_3),
% 0.21/0.56    inference(backward_demodulation,[],[f392,f442])).
% 0.21/0.56  fof(f442,plain,(
% 0.21/0.56    k1_xboole_0 = k1_relat_1(sK2) | ~spl4_3),
% 0.21/0.56    inference(backward_demodulation,[],[f431,f441])).
% 0.21/0.56  fof(f441,plain,(
% 0.21/0.56    k1_xboole_0 = k1_relat_1(k1_relat_1(k1_relat_1(sK2))) | ~spl4_3),
% 0.21/0.56    inference(backward_demodulation,[],[f432,f431])).
% 0.21/0.56  fof(f432,plain,(
% 0.21/0.56    k1_xboole_0 = k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(sK2))))) | ~spl4_3),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f281,f216])).
% 0.21/0.56  fof(f281,plain,(
% 0.21/0.56    v1_xboole_0(k1_relat_1(sK2)) | ~spl4_3),
% 0.21/0.56    inference(avatar_component_clause,[],[f279])).
% 0.21/0.56  fof(f431,plain,(
% 0.21/0.56    k1_relat_1(sK2) = k1_relat_1(k1_relat_1(k1_relat_1(sK2))) | ~spl4_3),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f281,f281,f207])).
% 0.21/0.56  fof(f392,plain,(
% 0.21/0.56    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f45,f61])).
% 0.21/0.56  fof(f521,plain,(
% 0.21/0.56    k1_relset_1(sK1,sK0,sK2) = k2_relset_1(sK0,sK1,k3_relset_1(sK1,sK0,sK2))),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f45,f66])).
% 0.21/0.56  fof(f66,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f30])).
% 0.21/0.56  fof(f529,plain,(
% 0.21/0.56    k2_relset_1(sK0,sK1,k3_relset_1(sK1,sK0,sK2)) = k2_relat_1(k3_relset_1(sK1,sK0,sK2))),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f499,f60])).
% 0.21/0.56  fof(f51,plain,(
% 0.21/0.56    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f23])).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.21/0.56    inference(flattening,[],[f22])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f10])).
% 0.21/0.56  fof(f10,axiom,(
% 0.21/0.56    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).
% 0.21/0.56  fof(f413,plain,(
% 0.21/0.56    spl4_3 | ~spl4_4),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f412])).
% 0.21/0.56  fof(f412,plain,(
% 0.21/0.56    $false | (spl4_3 | ~spl4_4)),
% 0.21/0.56    inference(subsumption_resolution,[],[f397,f410])).
% 0.21/0.56  fof(f410,plain,(
% 0.21/0.56    ~r2_hidden(sK3(k1_relat_1(sK2)),k1_relat_1(sK2)) | ~spl4_4),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f285,f395])).
% 0.21/0.56  fof(f395,plain,(
% 0.21/0.56    ( ! [X3] : (~m1_subset_1(X3,sK1) | ~r2_hidden(X3,k1_relat_1(sK2))) )),
% 0.21/0.56    inference(backward_demodulation,[],[f47,f392])).
% 0.21/0.56  fof(f47,plain,(
% 0.21/0.56    ( ! [X3] : (~m1_subset_1(X3,sK1) | ~r2_hidden(X3,k1_relset_1(sK1,sK0,sK2))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f36])).
% 0.21/0.56  fof(f285,plain,(
% 0.21/0.56    m1_subset_1(sK3(k1_relat_1(sK2)),sK1) | ~spl4_4),
% 0.21/0.56    inference(avatar_component_clause,[],[f283])).
% 0.21/0.56  fof(f283,plain,(
% 0.21/0.56    spl4_4 <=> m1_subset_1(sK3(k1_relat_1(sK2)),sK1)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.56  fof(f397,plain,(
% 0.21/0.56    r2_hidden(sK3(k1_relat_1(sK2)),k1_relat_1(sK2)) | spl4_3),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f280,f53])).
% 0.21/0.56  fof(f53,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f40])).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).
% 0.21/0.56  fof(f39,plain,(
% 0.21/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f38,plain,(
% 0.21/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.56    inference(rectify,[],[f37])).
% 0.21/0.56  fof(f37,plain,(
% 0.21/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.56    inference(nnf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.56  fof(f280,plain,(
% 0.21/0.56    ~v1_xboole_0(k1_relat_1(sK2)) | spl4_3),
% 0.21/0.56    inference(avatar_component_clause,[],[f279])).
% 0.21/0.56  fof(f286,plain,(
% 0.21/0.56    spl4_3 | spl4_4),
% 0.21/0.56    inference(avatar_split_clause,[],[f277,f283,f279])).
% 0.21/0.56  fof(f277,plain,(
% 0.21/0.56    m1_subset_1(sK3(k1_relat_1(sK2)),sK1) | v1_xboole_0(k1_relat_1(sK2))),
% 0.21/0.56    inference(resolution,[],[f276,f53])).
% 0.21/0.56  fof(f276,plain,(
% 0.21/0.56    ( ! [X4] : (~r2_hidden(X4,k1_relat_1(sK2)) | m1_subset_1(X4,sK1)) )),
% 0.21/0.56    inference(resolution,[],[f67,f245])).
% 0.21/0.56  fof(f245,plain,(
% 0.21/0.56    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f242,f58])).
% 0.21/0.56  fof(f58,plain,(
% 0.21/0.56    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f42])).
% 0.21/0.56  fof(f42,plain,(
% 0.21/0.56    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.56    inference(nnf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.56  fof(f242,plain,(
% 0.21/0.56    r1_tarski(k1_relat_1(sK2),sK1)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f188,f239,f55])).
% 0.21/0.56  fof(f55,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f41])).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.56    inference(nnf_transformation,[],[f24])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f7])).
% 0.21/0.56  fof(f7,axiom,(
% 0.21/0.56    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.56  fof(f239,plain,(
% 0.21/0.56    v4_relat_1(sK2,sK1)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f45,f63])).
% 0.21/0.56  fof(f63,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f29])).
% 0.21/0.56  fof(f29,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(ennf_transformation,[],[f11])).
% 0.21/0.56  fof(f11,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.56  fof(f188,plain,(
% 0.21/0.56    v1_relat_1(sK2)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f54,f45,f49])).
% 0.21/0.56  fof(f67,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f32])).
% 0.21/0.56  fof(f32,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.56    inference(flattening,[],[f31])).
% 0.21/0.56  fof(f31,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.56    inference(ennf_transformation,[],[f5])).
% 0.21/0.56  fof(f5,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (10527)------------------------------
% 0.21/0.56  % (10527)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (10527)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (10527)Memory used [KB]: 10874
% 0.21/0.56  % (10527)Time elapsed: 0.123 s
% 0.21/0.56  % (10527)------------------------------
% 0.21/0.56  % (10527)------------------------------
% 0.21/0.57  % (10517)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.57  % (10515)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.57  % (10512)Success in time 0.202 s
%------------------------------------------------------------------------------
