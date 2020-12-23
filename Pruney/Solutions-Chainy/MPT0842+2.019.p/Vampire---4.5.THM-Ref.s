%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 830 expanded)
%              Number of leaves         :   10 ( 176 expanded)
%              Depth                    :   22
%              Number of atoms          :  180 (3416 expanded)
%              Number of equality atoms :    7 ( 112 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f173,plain,(
    $false ),
    inference(subsumption_resolution,[],[f172,f168])).

fof(f168,plain,(
    r2_hidden(sK10(sK4,sK1,sK3),sK2) ),
    inference(resolution,[],[f163,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X0),sK3)
      | r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f46,f65])).

fof(f65,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_zfmisc_1(sK0,sK2))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f35,f51])).

fof(f51,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) ),
    inference(resolution,[],[f39,f25])).

fof(f25,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
          <~> ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X4,X5),X3)
                & m1_subset_1(X5,X2) ) )
          & m1_subset_1(X4,X0) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => ! [X4] :
            ( m1_subset_1(X4,X0)
           => ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
            <=> ? [X5] :
                  ( r2_hidden(X5,X1)
                  & r2_hidden(k4_tarski(X4,X5),X3)
                  & m1_subset_1(X5,X2) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ~ v1_xboole_0(X2)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                   => ! [X4] :
                        ( m1_subset_1(X4,X0)
                       => ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
                        <=> ? [X5] :
                              ( r2_hidden(X5,X1)
                              & r2_hidden(k4_tarski(X4,X5),X3)
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
                  ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                 => ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X4,X5),X3)
                            & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_relset_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
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

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f163,plain,(
    r2_hidden(k4_tarski(sK4,sK10(sK4,sK1,sK3)),sK3) ),
    inference(subsumption_resolution,[],[f160,f58])).

fof(f58,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f54,f25])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f26,f33])).

fof(f33,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f160,plain,
    ( r2_hidden(k4_tarski(sK4,sK10(sK4,sK1,sK3)),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f159,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | r2_hidden(k4_tarski(X0,sK10(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(f159,plain,(
    r2_hidden(sK4,k10_relat_1(sK3,sK1)) ),
    inference(duplicate_literal_removal,[],[f156])).

fof(f156,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | r2_hidden(sK4,k10_relat_1(sK3,sK1)) ),
    inference(resolution,[],[f152,f139])).

fof(f139,plain,(
    r2_hidden(sK5,sK1) ),
    inference(subsumption_resolution,[],[f138,f134])).

fof(f134,plain,
    ( r2_hidden(sK10(sK4,sK1,sK3),sK2)
    | r2_hidden(sK5,sK1) ),
    inference(resolution,[],[f109,f76])).

fof(f109,plain,
    ( r2_hidden(k4_tarski(sK4,sK10(sK4,sK1,sK3)),sK3)
    | r2_hidden(sK5,sK1) ),
    inference(subsumption_resolution,[],[f106,f58])).

fof(f106,plain,
    ( r2_hidden(sK5,sK1)
    | r2_hidden(k4_tarski(sK4,sK10(sK4,sK1,sK3)),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f99,f41])).

fof(f99,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | r2_hidden(sK5,sK1) ),
    inference(backward_demodulation,[],[f23,f93])).

fof(f93,plain,(
    ! [X0] : k8_relset_1(sK0,sK2,sK3,X0) = k10_relat_1(sK3,X0) ),
    inference(resolution,[],[f44,f25])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f23,plain,
    ( r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))
    | r2_hidden(sK5,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f138,plain,
    ( r2_hidden(sK5,sK1)
    | ~ r2_hidden(sK10(sK4,sK1,sK3),sK2) ),
    inference(resolution,[],[f137,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f137,plain,
    ( ~ m1_subset_1(sK10(sK4,sK1,sK3),sK2)
    | r2_hidden(sK5,sK1) ),
    inference(subsumption_resolution,[],[f136,f111])).

fof(f111,plain,
    ( r2_hidden(sK10(sK4,sK1,sK3),sK1)
    | r2_hidden(sK5,sK1) ),
    inference(subsumption_resolution,[],[f108,f58])).

fof(f108,plain,
    ( r2_hidden(sK5,sK1)
    | r2_hidden(sK10(sK4,sK1,sK3),sK1)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f99,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | r2_hidden(sK10(X0,X1,X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f136,plain,
    ( r2_hidden(sK5,sK1)
    | ~ m1_subset_1(sK10(sK4,sK1,sK3),sK2)
    | ~ r2_hidden(sK10(sK4,sK1,sK3),sK1) ),
    inference(subsumption_resolution,[],[f133,f99])).

fof(f133,plain,
    ( r2_hidden(sK5,sK1)
    | ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ m1_subset_1(sK10(sK4,sK1,sK3),sK2)
    | ~ r2_hidden(sK10(sK4,sK1,sK3),sK1) ),
    inference(resolution,[],[f109,f96])).

fof(f96,plain,(
    ! [X5] :
      ( ~ r2_hidden(k4_tarski(sK4,X5),sK3)
      | ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
      | ~ m1_subset_1(X5,sK2)
      | ~ r2_hidden(X5,sK1) ) ),
    inference(backward_demodulation,[],[f20,f93])).

fof(f20,plain,(
    ! [X5] :
      ( ~ r2_hidden(k4_tarski(sK4,X5),sK3)
      | ~ m1_subset_1(X5,sK2)
      | ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f152,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5,X0)
      | r2_hidden(sK4,k10_relat_1(sK3,X0))
      | r2_hidden(sK4,k10_relat_1(sK3,sK1)) ) ),
    inference(resolution,[],[f148,f98])).

fof(f98,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),sK3)
    | r2_hidden(sK4,k10_relat_1(sK3,sK1)) ),
    inference(backward_demodulation,[],[f22,f93])).

fof(f22,plain,
    ( r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))
    | r2_hidden(k4_tarski(sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f13])).

fof(f148,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),sK3)
      | ~ r2_hidden(X6,X7)
      | r2_hidden(X5,k10_relat_1(sK3,X7)) ) ),
    inference(resolution,[],[f48,f58])).

fof(f48,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

fof(f172,plain,(
    ~ r2_hidden(sK10(sK4,sK1,sK3),sK2) ),
    inference(resolution,[],[f171,f34])).

fof(f171,plain,(
    ~ m1_subset_1(sK10(sK4,sK1,sK3),sK2) ),
    inference(subsumption_resolution,[],[f170,f165])).

fof(f165,plain,(
    r2_hidden(sK10(sK4,sK1,sK3),sK1) ),
    inference(subsumption_resolution,[],[f162,f58])).

fof(f162,plain,
    ( r2_hidden(sK10(sK4,sK1,sK3),sK1)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f159,f42])).

fof(f170,plain,
    ( ~ m1_subset_1(sK10(sK4,sK1,sK3),sK2)
    | ~ r2_hidden(sK10(sK4,sK1,sK3),sK1) ),
    inference(subsumption_resolution,[],[f166,f159])).

fof(f166,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ m1_subset_1(sK10(sK4,sK1,sK3),sK2)
    | ~ r2_hidden(sK10(sK4,sK1,sK3),sK1) ),
    inference(resolution,[],[f163,f96])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:05:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.53  % (7527)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (7534)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (7526)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (7519)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (7519)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f173,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(subsumption_resolution,[],[f172,f168])).
% 0.21/0.54  fof(f168,plain,(
% 0.21/0.54    r2_hidden(sK10(sK4,sK1,sK3),sK2)),
% 0.21/0.54    inference(resolution,[],[f163,f76])).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X1,X0),sK3) | r2_hidden(X0,sK2)) )),
% 0.21/0.54    inference(resolution,[],[f46,f65])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(sK0,sK2)) | ~r2_hidden(X0,sK3)) )),
% 0.21/0.54    inference(resolution,[],[f35,f51])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    r1_tarski(sK3,k2_zfmisc_1(sK0,sK2))),
% 0.21/0.54    inference(resolution,[],[f39,f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ? [X0,X1,X2,X3] : (? [X4] : ((r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <~> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2)))))),
% 0.21/0.54    inference(pure_predicate_removal,[],[f11])).
% 0.21/0.54  fof(f11,negated_conjecture,(
% 0.21/0.54    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))))))))),
% 0.21/0.54    inference(negated_conjecture,[],[f10])).
% 0.21/0.54  fof(f10,conjecture,(
% 0.21/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))))))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_relset_1)).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f17])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.21/0.55  fof(f163,plain,(
% 0.21/0.55    r2_hidden(k4_tarski(sK4,sK10(sK4,sK1,sK3)),sK3)),
% 0.21/0.55    inference(subsumption_resolution,[],[f160,f58])).
% 0.21/0.55  fof(f58,plain,(
% 0.21/0.55    v1_relat_1(sK3)),
% 0.21/0.55    inference(resolution,[],[f54,f25])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) )),
% 0.21/0.55    inference(resolution,[],[f26,f33])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f14])).
% 0.21/0.55  fof(f14,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.55  fof(f160,plain,(
% 0.21/0.55    r2_hidden(k4_tarski(sK4,sK10(sK4,sK1,sK3)),sK3) | ~v1_relat_1(sK3)),
% 0.21/0.55    inference(resolution,[],[f159,f41])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(k4_tarski(X0,sK10(X0,X1,X2)),X2) | ~v1_relat_1(X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.55    inference(ennf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).
% 0.21/0.55  fof(f159,plain,(
% 0.21/0.55    r2_hidden(sK4,k10_relat_1(sK3,sK1))),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f156])).
% 0.21/0.55  fof(f156,plain,(
% 0.21/0.55    r2_hidden(sK4,k10_relat_1(sK3,sK1)) | r2_hidden(sK4,k10_relat_1(sK3,sK1))),
% 0.21/0.55    inference(resolution,[],[f152,f139])).
% 0.21/0.55  fof(f139,plain,(
% 0.21/0.55    r2_hidden(sK5,sK1)),
% 0.21/0.55    inference(subsumption_resolution,[],[f138,f134])).
% 0.21/0.55  fof(f134,plain,(
% 0.21/0.55    r2_hidden(sK10(sK4,sK1,sK3),sK2) | r2_hidden(sK5,sK1)),
% 0.21/0.55    inference(resolution,[],[f109,f76])).
% 0.21/0.55  fof(f109,plain,(
% 0.21/0.55    r2_hidden(k4_tarski(sK4,sK10(sK4,sK1,sK3)),sK3) | r2_hidden(sK5,sK1)),
% 0.21/0.55    inference(subsumption_resolution,[],[f106,f58])).
% 0.21/0.55  fof(f106,plain,(
% 0.21/0.55    r2_hidden(sK5,sK1) | r2_hidden(k4_tarski(sK4,sK10(sK4,sK1,sK3)),sK3) | ~v1_relat_1(sK3)),
% 0.21/0.55    inference(resolution,[],[f99,f41])).
% 0.21/0.55  fof(f99,plain,(
% 0.21/0.55    r2_hidden(sK4,k10_relat_1(sK3,sK1)) | r2_hidden(sK5,sK1)),
% 0.21/0.55    inference(backward_demodulation,[],[f23,f93])).
% 0.21/0.55  fof(f93,plain,(
% 0.21/0.55    ( ! [X0] : (k8_relset_1(sK0,sK2,sK3,X0) = k10_relat_1(sK3,X0)) )),
% 0.21/0.55    inference(resolution,[],[f44,f25])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.55    inference(ennf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) | r2_hidden(sK5,sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f13])).
% 0.21/0.55  fof(f138,plain,(
% 0.21/0.55    r2_hidden(sK5,sK1) | ~r2_hidden(sK10(sK4,sK1,sK3),sK2)),
% 0.21/0.55    inference(resolution,[],[f137,f34])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.55  fof(f137,plain,(
% 0.21/0.55    ~m1_subset_1(sK10(sK4,sK1,sK3),sK2) | r2_hidden(sK5,sK1)),
% 0.21/0.55    inference(subsumption_resolution,[],[f136,f111])).
% 0.21/0.55  fof(f111,plain,(
% 0.21/0.55    r2_hidden(sK10(sK4,sK1,sK3),sK1) | r2_hidden(sK5,sK1)),
% 0.21/0.55    inference(subsumption_resolution,[],[f108,f58])).
% 0.21/0.55  fof(f108,plain,(
% 0.21/0.55    r2_hidden(sK5,sK1) | r2_hidden(sK10(sK4,sK1,sK3),sK1) | ~v1_relat_1(sK3)),
% 0.21/0.55    inference(resolution,[],[f99,f42])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(sK10(X0,X1,X2),X1) | ~v1_relat_1(X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  fof(f136,plain,(
% 0.21/0.55    r2_hidden(sK5,sK1) | ~m1_subset_1(sK10(sK4,sK1,sK3),sK2) | ~r2_hidden(sK10(sK4,sK1,sK3),sK1)),
% 0.21/0.55    inference(subsumption_resolution,[],[f133,f99])).
% 0.21/0.55  fof(f133,plain,(
% 0.21/0.55    r2_hidden(sK5,sK1) | ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~m1_subset_1(sK10(sK4,sK1,sK3),sK2) | ~r2_hidden(sK10(sK4,sK1,sK3),sK1)),
% 0.21/0.55    inference(resolution,[],[f109,f96])).
% 0.21/0.55  fof(f96,plain,(
% 0.21/0.55    ( ! [X5] : (~r2_hidden(k4_tarski(sK4,X5),sK3) | ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~m1_subset_1(X5,sK2) | ~r2_hidden(X5,sK1)) )),
% 0.21/0.55    inference(backward_demodulation,[],[f20,f93])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ( ! [X5] : (~r2_hidden(k4_tarski(sK4,X5),sK3) | ~m1_subset_1(X5,sK2) | ~r2_hidden(X5,sK1) | ~r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f13])).
% 0.21/0.55  fof(f152,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(sK5,X0) | r2_hidden(sK4,k10_relat_1(sK3,X0)) | r2_hidden(sK4,k10_relat_1(sK3,sK1))) )),
% 0.21/0.55    inference(resolution,[],[f148,f98])).
% 0.21/0.55  fof(f98,plain,(
% 0.21/0.55    r2_hidden(k4_tarski(sK4,sK5),sK3) | r2_hidden(sK4,k10_relat_1(sK3,sK1))),
% 0.21/0.55    inference(backward_demodulation,[],[f22,f93])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) | r2_hidden(k4_tarski(sK4,sK5),sK3)),
% 0.21/0.55    inference(cnf_transformation,[],[f13])).
% 0.21/0.55  fof(f148,plain,(
% 0.21/0.55    ( ! [X6,X7,X5] : (~r2_hidden(k4_tarski(X5,X6),sK3) | ~r2_hidden(X6,X7) | r2_hidden(X5,k10_relat_1(sK3,X7))) )),
% 0.21/0.55    inference(resolution,[],[f48,f58])).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    ( ! [X4,X0,X3,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X4,X1) | r2_hidden(X3,k10_relat_1(X0,X1))) )),
% 0.21/0.55    inference(equality_resolution,[],[f32])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X4,X1) | r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 0.21/0.55    inference(cnf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).
% 0.21/0.55  fof(f172,plain,(
% 0.21/0.55    ~r2_hidden(sK10(sK4,sK1,sK3),sK2)),
% 0.21/0.55    inference(resolution,[],[f171,f34])).
% 0.21/0.55  fof(f171,plain,(
% 0.21/0.55    ~m1_subset_1(sK10(sK4,sK1,sK3),sK2)),
% 0.21/0.55    inference(subsumption_resolution,[],[f170,f165])).
% 0.21/0.55  fof(f165,plain,(
% 0.21/0.55    r2_hidden(sK10(sK4,sK1,sK3),sK1)),
% 0.21/0.55    inference(subsumption_resolution,[],[f162,f58])).
% 0.21/0.55  fof(f162,plain,(
% 0.21/0.55    r2_hidden(sK10(sK4,sK1,sK3),sK1) | ~v1_relat_1(sK3)),
% 0.21/0.55    inference(resolution,[],[f159,f42])).
% 0.21/0.55  fof(f170,plain,(
% 0.21/0.55    ~m1_subset_1(sK10(sK4,sK1,sK3),sK2) | ~r2_hidden(sK10(sK4,sK1,sK3),sK1)),
% 0.21/0.55    inference(subsumption_resolution,[],[f166,f159])).
% 0.21/0.55  fof(f166,plain,(
% 0.21/0.55    ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~m1_subset_1(sK10(sK4,sK1,sK3),sK2) | ~r2_hidden(sK10(sK4,sK1,sK3),sK1)),
% 0.21/0.55    inference(resolution,[],[f163,f96])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (7519)------------------------------
% 0.21/0.55  % (7519)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (7519)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (7519)Memory used [KB]: 6396
% 0.21/0.55  % (7519)Time elapsed: 0.044 s
% 0.21/0.55  % (7519)------------------------------
% 0.21/0.55  % (7519)------------------------------
% 0.21/0.55  % (7512)Success in time 0.188 s
%------------------------------------------------------------------------------
