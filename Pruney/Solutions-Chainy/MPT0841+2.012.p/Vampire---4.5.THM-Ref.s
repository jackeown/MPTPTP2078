%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 144 expanded)
%              Number of leaves         :   13 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :  173 ( 563 expanded)
%              Number of equality atoms :    9 (  24 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f220,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f112,f136,f193,f219])).

fof(f219,plain,
    ( spl10_2
    | ~ spl10_3
    | ~ spl10_4 ),
    inference(avatar_contradiction_clause,[],[f211])).

fof(f211,plain,
    ( $false
    | spl10_2
    | ~ spl10_3
    | ~ spl10_4 ),
    inference(unit_resulting_resolution,[],[f50,f89,f69,f111,f45])).

fof(f45,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).

fof(f111,plain,
    ( r2_hidden(k4_tarski(sK5,sK4),sK3)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl10_4
  <=> r2_hidden(k4_tarski(sK5,sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f69,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | spl10_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl10_2
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f89,plain,
    ( r2_hidden(sK5,sK1)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl10_3
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f50,plain,(
    v1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f41,f23,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f23,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <~> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) )
                      & m1_subset_1(X4,X0) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ~ v1_xboole_0(X2)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                   => ! [X4] :
                        ( m1_subset_1(X4,X0)
                       => ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                        <=> ? [X5] :
                              ( r2_hidden(X5,X1)
                              & r2_hidden(k4_tarski(X5,X4),X3)
                              & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                 => ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relset_1)).

fof(f41,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f193,plain,
    ( ~ spl10_2
    | ~ spl10_7 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | ~ spl10_2
    | ~ spl10_7 ),
    inference(unit_resulting_resolution,[],[f162,f150,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f150,plain,
    ( r2_hidden(sK7(sK3,sK1,sK4),sK2)
    | ~ spl10_2 ),
    inference(unit_resulting_resolution,[],[f100,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f100,plain,
    ( r2_hidden(k4_tarski(sK7(sK3,sK1,sK4),sK4),k2_zfmisc_1(sK2,sK0))
    | ~ spl10_2 ),
    inference(unit_resulting_resolution,[],[f49,f72,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f72,plain,
    ( r2_hidden(k4_tarski(sK7(sK3,sK1,sK4),sK4),sK3)
    | ~ spl10_2 ),
    inference(unit_resulting_resolution,[],[f50,f70,f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK7(X0,X1,X3),X3),X0)
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK7(X0,X1,X3),X3),X0)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f70,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f49,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK2,sK0)) ),
    inference(unit_resulting_resolution,[],[f23,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f162,plain,
    ( ~ m1_subset_1(sK7(sK3,sK1,sK4),sK2)
    | ~ spl10_2
    | ~ spl10_7 ),
    inference(unit_resulting_resolution,[],[f73,f72,f135])).

fof(f135,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,sK2)
        | ~ r2_hidden(X5,sK1)
        | ~ r2_hidden(k4_tarski(X5,sK4),sK3) )
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl10_7
  <=> ! [X5] :
        ( ~ m1_subset_1(X5,sK2)
        | ~ r2_hidden(X5,sK1)
        | ~ r2_hidden(k4_tarski(X5,sK4),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f73,plain,
    ( r2_hidden(sK7(sK3,sK1,sK4),sK1)
    | ~ spl10_2 ),
    inference(unit_resulting_resolution,[],[f50,f70,f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK7(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK7(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f136,plain,
    ( spl10_7
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f51,f68,f134])).

fof(f51,plain,(
    ! [X5] :
      ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
      | ~ m1_subset_1(X5,sK2)
      | ~ r2_hidden(k4_tarski(X5,sK4),sK3)
      | ~ r2_hidden(X5,sK1) ) ),
    inference(backward_demodulation,[],[f18,f48])).

fof(f48,plain,(
    ! [X0] : k7_relset_1(sK2,sK0,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(unit_resulting_resolution,[],[f23,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f18,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,sK2)
      | ~ r2_hidden(k4_tarski(X5,sK4),sK3)
      | ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f112,plain,
    ( spl10_4
    | spl10_2 ),
    inference(avatar_split_clause,[],[f53,f68,f109])).

fof(f53,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | r2_hidden(k4_tarski(sK5,sK4),sK3) ),
    inference(backward_demodulation,[],[f20,f48])).

fof(f20,plain,
    ( r2_hidden(k4_tarski(sK5,sK4),sK3)
    | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f90,plain,
    ( spl10_3
    | spl10_2 ),
    inference(avatar_split_clause,[],[f54,f68,f87])).

fof(f54,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | r2_hidden(sK5,sK1) ),
    inference(backward_demodulation,[],[f21,f48])).

fof(f21,plain,
    ( r2_hidden(sK5,sK1)
    | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:26:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (17236)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (17236)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (17252)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f220,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f90,f112,f136,f193,f219])).
% 0.21/0.49  fof(f219,plain,(
% 0.21/0.49    spl10_2 | ~spl10_3 | ~spl10_4),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f211])).
% 0.21/0.49  fof(f211,plain,(
% 0.21/0.49    $false | (spl10_2 | ~spl10_3 | ~spl10_4)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f50,f89,f69,f111,f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X4,X0,X3,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(X4,X1) | r2_hidden(X3,k9_relat_1(X0,X1))) )),
% 0.21/0.49    inference(equality_resolution,[],[f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(X4,X1) | r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK5,sK4),sK3) | ~spl10_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f109])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    spl10_4 <=> r2_hidden(k4_tarski(sK5,sK4),sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | spl10_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f68])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    spl10_2 <=> r2_hidden(sK4,k9_relat_1(sK3,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    r2_hidden(sK5,sK1) | ~spl10_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f87])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    spl10_3 <=> r2_hidden(sK5,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    v1_relat_1(sK3)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f41,f23,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <~> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 0.21/0.49    inference(negated_conjecture,[],[f10])).
% 0.21/0.49  fof(f10,conjecture,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relset_1)).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.49  fof(f193,plain,(
% 0.21/0.49    ~spl10_2 | ~spl10_7),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f190])).
% 0.21/0.49  fof(f190,plain,(
% 0.21/0.49    $false | (~spl10_2 | ~spl10_7)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f162,f150,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.49  fof(f150,plain,(
% 0.21/0.49    r2_hidden(sK7(sK3,sK1,sK4),sK2) | ~spl10_2),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f100,f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK7(sK3,sK1,sK4),sK4),k2_zfmisc_1(sK2,sK0)) | ~spl10_2),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f49,f72,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK7(sK3,sK1,sK4),sK4),sK3) | ~spl10_2),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f50,f70,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK7(X0,X1,X3),X3),X0) | ~r2_hidden(X3,k9_relat_1(X0,X1))) )),
% 0.21/0.49    inference(equality_resolution,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK7(X0,X1,X3),X3),X0) | ~r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    r2_hidden(sK4,k9_relat_1(sK3,sK1)) | ~spl10_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f68])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    r1_tarski(sK3,k2_zfmisc_1(sK2,sK0))),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f23,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    ~m1_subset_1(sK7(sK3,sK1,sK4),sK2) | (~spl10_2 | ~spl10_7)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f73,f72,f135])).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    ( ! [X5] : (~m1_subset_1(X5,sK2) | ~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(X5,sK4),sK3)) ) | ~spl10_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f134])).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    spl10_7 <=> ! [X5] : (~m1_subset_1(X5,sK2) | ~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(X5,sK4),sK3))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    r2_hidden(sK7(sK3,sK1,sK4),sK1) | ~spl10_2),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f50,f70,f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | r2_hidden(sK7(X0,X1,X3),X1) | ~r2_hidden(X3,k9_relat_1(X0,X1))) )),
% 0.21/0.49    inference(equality_resolution,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | r2_hidden(sK7(X0,X1,X3),X1) | ~r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f136,plain,(
% 0.21/0.49    spl10_7 | ~spl10_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f51,f68,f134])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X5] : (~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | ~m1_subset_1(X5,sK2) | ~r2_hidden(k4_tarski(X5,sK4),sK3) | ~r2_hidden(X5,sK1)) )),
% 0.21/0.49    inference(backward_demodulation,[],[f18,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X0] : (k7_relset_1(sK2,sK0,sK3,X0) = k9_relat_1(sK3,X0)) )),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f23,f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ( ! [X5] : (~m1_subset_1(X5,sK2) | ~r2_hidden(k4_tarski(X5,sK4),sK3) | ~r2_hidden(X5,sK1) | ~r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    spl10_4 | spl10_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f53,f68,f109])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    r2_hidden(sK4,k9_relat_1(sK3,sK1)) | r2_hidden(k4_tarski(sK5,sK4),sK3)),
% 0.21/0.49    inference(backward_demodulation,[],[f20,f48])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK5,sK4),sK3) | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    spl10_3 | spl10_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f54,f68,f87])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    r2_hidden(sK4,k9_relat_1(sK3,sK1)) | r2_hidden(sK5,sK1)),
% 0.21/0.49    inference(backward_demodulation,[],[f21,f48])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    r2_hidden(sK5,sK1) | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (17236)------------------------------
% 0.21/0.49  % (17236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (17236)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (17236)Memory used [KB]: 6396
% 0.21/0.49  % (17236)Time elapsed: 0.068 s
% 0.21/0.49  % (17236)------------------------------
% 0.21/0.49  % (17236)------------------------------
% 0.21/0.49  % (17226)Success in time 0.13 s
%------------------------------------------------------------------------------
