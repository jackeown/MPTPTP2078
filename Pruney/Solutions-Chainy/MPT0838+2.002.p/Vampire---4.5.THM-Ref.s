%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 351 expanded)
%              Number of leaves         :   15 (  88 expanded)
%              Depth                    :   15
%              Number of atoms          :  179 ( 986 expanded)
%              Number of equality atoms :   20 ( 124 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f355,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f109,f241,f354])).

fof(f354,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f349])).

fof(f349,plain,
    ( $false
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f264,f334,f77])).

fof(f77,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK2),X0)
      | ~ r1_tarski(sK2,X0) ) ),
    inference(resolution,[],[f71,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f71,plain,(
    r2_hidden(sK4(sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f69,f37])).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f69,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(unit_resulting_resolution,[],[f66,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

fof(f66,plain,(
    ~ v1_xboole_0(k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f64,f61])).

fof(f61,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f29,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f29,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(X0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(X0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,X1)
                       => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                    & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                  & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).

fof(f64,plain,(
    ~ v1_xboole_0(k1_relset_1(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f30,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f30,plain,(
    k1_xboole_0 != k1_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f334,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl5_1 ),
    inference(backward_demodulation,[],[f252,f325])).

fof(f325,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f265,f41])).

fof(f265,plain,
    ( ! [X0] : v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0))
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f243,f244])).

fof(f244,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f104,f41])).

fof(f104,plain,
    ( v1_xboole_0(k2_relat_1(sK2))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl5_1
  <=> v1_xboole_0(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f243,plain,
    ( ! [X0] : v1_xboole_0(k2_zfmisc_1(X0,k2_relat_1(sK2)))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f104,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

fof(f252,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))
    | ~ spl5_1 ),
    inference(backward_demodulation,[],[f67,f244])).

fof(f67,plain,(
    r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) ),
    inference(unit_resulting_resolution,[],[f60,f47])).

fof(f47,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(f60,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f29,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f264,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl5_1 ),
    inference(backward_demodulation,[],[f245,f244])).

fof(f245,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_relat_1(sK2))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f104,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f241,plain,(
    spl5_2 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f139,f219,f77])).

fof(f219,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | spl5_2 ),
    inference(backward_demodulation,[],[f125,f210])).

fof(f210,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f140,f41])).

fof(f140,plain,
    ( ! [X0] : v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0))
    | spl5_2 ),
    inference(forward_demodulation,[],[f116,f117])).

fof(f117,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f113,f41])).

fof(f113,plain,
    ( v1_xboole_0(k2_relat_1(sK2))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f112,f37])).

fof(f112,plain,
    ( ~ r2_hidden(sK4(k2_relat_1(sK2)),k2_relat_1(sK2))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f68,f110,f33])).

fof(f110,plain,
    ( ~ r2_hidden(sK4(k2_relat_1(sK2)),sK1)
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f108,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f108,plain,
    ( ~ m1_subset_1(sK4(k2_relat_1(sK2)),sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl5_2
  <=> m1_subset_1(sK4(k2_relat_1(sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f68,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f60,f59,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f59,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f29,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f116,plain,
    ( ! [X0] : v1_xboole_0(k2_zfmisc_1(X0,k2_relat_1(sK2)))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f113,f43])).

fof(f125,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))
    | spl5_2 ),
    inference(backward_demodulation,[],[f67,f117])).

fof(f139,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | spl5_2 ),
    inference(backward_demodulation,[],[f118,f117])).

fof(f118,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_relat_1(sK2))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f113,f38])).

fof(f109,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f73,f106,f102])).

fof(f73,plain,
    ( ~ m1_subset_1(sK4(k2_relat_1(sK2)),sK1)
    | v1_xboole_0(k2_relat_1(sK2)) ),
    inference(resolution,[],[f63,f37])).

fof(f63,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_relat_1(sK2))
      | ~ m1_subset_1(X3,sK1) ) ),
    inference(backward_demodulation,[],[f28,f62])).

fof(f62,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f29,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f28,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK1)
      | ~ r2_hidden(X3,k2_relset_1(sK0,sK1,sK2)) ) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:01:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (602)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (602)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f355,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f109,f241,f354])).
% 0.21/0.50  fof(f354,plain,(
% 0.21/0.50    ~spl5_1),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f349])).
% 0.21/0.50  fof(f349,plain,(
% 0.21/0.50    $false | ~spl5_1),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f264,f334,f77])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK4(sK2),X0) | ~r1_tarski(sK2,X0)) )),
% 0.21/0.50    inference(resolution,[],[f71,f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    r2_hidden(sK4(sK2),sK2)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f69,f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ~v1_xboole_0(sK2)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f66,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_xboole_0(X0) | v1_xboole_0(k1_relat_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    ~v1_xboole_0(k1_relat_1(sK2))),
% 0.21/0.50    inference(forward_demodulation,[],[f64,f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f29,f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.50    inference(flattening,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,negated_conjecture,(
% 0.21/0.50    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 0.21/0.50    inference(negated_conjecture,[],[f13])).
% 0.21/0.50  fof(f13,conjecture,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ~v1_xboole_0(k1_relset_1(sK0,sK1,sK2))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f30,f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    k1_xboole_0 != k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f334,plain,(
% 0.21/0.50    r1_tarski(sK2,k1_xboole_0) | ~spl5_1),
% 0.21/0.50    inference(backward_demodulation,[],[f252,f325])).
% 0.21/0.50  fof(f325,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | ~spl5_1),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f265,f41])).
% 0.21/0.50  fof(f265,plain,(
% 0.21/0.50    ( ! [X0] : (v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0))) ) | ~spl5_1),
% 0.21/0.50    inference(forward_demodulation,[],[f243,f244])).
% 0.21/0.50  fof(f244,plain,(
% 0.21/0.50    k1_xboole_0 = k2_relat_1(sK2) | ~spl5_1),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f104,f41])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    v1_xboole_0(k2_relat_1(sK2)) | ~spl5_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f102])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    spl5_1 <=> v1_xboole_0(k2_relat_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.50  fof(f243,plain,(
% 0.21/0.50    ( ! [X0] : (v1_xboole_0(k2_zfmisc_1(X0,k2_relat_1(sK2)))) ) | ~spl5_1),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f104,f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_xboole_0(X1) | v1_xboole_0(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).
% 0.21/0.50  fof(f252,plain,(
% 0.21/0.50    r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)) | ~spl5_1),
% 0.21/0.50    inference(backward_demodulation,[],[f67,f244])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f60,f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    v1_relat_1(sK2)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f29,f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.50  fof(f264,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl5_1),
% 0.21/0.50    inference(backward_demodulation,[],[f245,f244])).
% 0.21/0.50  fof(f245,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK2))) ) | ~spl5_1),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f104,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f241,plain,(
% 0.21/0.50    spl5_2),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f236])).
% 0.21/0.50  fof(f236,plain,(
% 0.21/0.50    $false | spl5_2),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f139,f219,f77])).
% 0.21/0.50  fof(f219,plain,(
% 0.21/0.50    r1_tarski(sK2,k1_xboole_0) | spl5_2),
% 0.21/0.50    inference(backward_demodulation,[],[f125,f210])).
% 0.21/0.50  fof(f210,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | spl5_2),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f140,f41])).
% 0.21/0.50  fof(f140,plain,(
% 0.21/0.50    ( ! [X0] : (v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0))) ) | spl5_2),
% 0.21/0.50    inference(forward_demodulation,[],[f116,f117])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    k1_xboole_0 = k2_relat_1(sK2) | spl5_2),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f113,f41])).
% 0.21/0.50  fof(f113,plain,(
% 0.21/0.50    v1_xboole_0(k2_relat_1(sK2)) | spl5_2),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f112,f37])).
% 0.21/0.50  fof(f112,plain,(
% 0.21/0.50    ~r2_hidden(sK4(k2_relat_1(sK2)),k2_relat_1(sK2)) | spl5_2),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f68,f110,f33])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    ~r2_hidden(sK4(k2_relat_1(sK2)),sK1) | spl5_2),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f108,f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    ~m1_subset_1(sK4(k2_relat_1(sK2)),sK1) | spl5_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f106])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    spl5_2 <=> m1_subset_1(sK4(k2_relat_1(sK2)),sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    r1_tarski(k2_relat_1(sK2),sK1)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f60,f59,f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    v5_relat_1(sK2,sK1)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f29,f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.50  fof(f116,plain,(
% 0.21/0.50    ( ! [X0] : (v1_xboole_0(k2_zfmisc_1(X0,k2_relat_1(sK2)))) ) | spl5_2),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f113,f43])).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)) | spl5_2),
% 0.21/0.50    inference(backward_demodulation,[],[f67,f117])).
% 0.21/0.50  fof(f139,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | spl5_2),
% 0.21/0.50    inference(backward_demodulation,[],[f118,f117])).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK2))) ) | spl5_2),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f113,f38])).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    spl5_1 | ~spl5_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f73,f106,f102])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ~m1_subset_1(sK4(k2_relat_1(sK2)),sK1) | v1_xboole_0(k2_relat_1(sK2))),
% 0.21/0.50    inference(resolution,[],[f63,f37])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X3] : (~r2_hidden(X3,k2_relat_1(sK2)) | ~m1_subset_1(X3,sK1)) )),
% 0.21/0.50    inference(backward_demodulation,[],[f28,f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f29,f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ( ! [X3] : (~m1_subset_1(X3,sK1) | ~r2_hidden(X3,k2_relset_1(sK0,sK1,sK2))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (602)------------------------------
% 0.21/0.50  % (602)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (602)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (602)Memory used [KB]: 6268
% 0.21/0.50  % (609)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.50  % (602)Time elapsed: 0.074 s
% 0.21/0.51  % (602)------------------------------
% 0.21/0.51  % (602)------------------------------
% 0.21/0.51  % (594)Success in time 0.14 s
%------------------------------------------------------------------------------
