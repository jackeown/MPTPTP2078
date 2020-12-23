%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t35_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:05 EDT 2019

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 244 expanded)
%              Number of leaves         :   23 (  92 expanded)
%              Depth                    :    9
%              Number of atoms          :  278 ( 601 expanded)
%              Number of equality atoms :   60 ( 175 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f349,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f76,f81,f95,f100,f107,f118,f122,f141,f172,f179,f194,f243,f250,f265,f272,f321,f341])).

fof(f341,plain,
    ( ~ spl9_6
    | spl9_9
    | ~ spl9_26 ),
    inference(avatar_contradiction_clause,[],[f340])).

fof(f340,plain,
    ( $false
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_26 ),
    inference(subsumption_resolution,[],[f336,f45])).

fof(f45,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t35_zfmisc_1.p',d1_tarski)).

fof(f336,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k1_tarski(k4_tarski(sK0,sK1)))
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_26 ),
    inference(backward_demodulation,[],[f329,f94])).

fof(f94,plain,
    ( ~ r2_hidden(sK8(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(k4_tarski(sK0,sK1))),k1_tarski(k4_tarski(sK0,sK1)))
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl9_9
  <=> ~ r2_hidden(sK8(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(k4_tarski(sK0,sK1))),k1_tarski(k4_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f329,plain,
    ( k4_tarski(sK0,sK1) = sK8(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(k4_tarski(sK0,sK1)))
    | ~ spl9_6
    | ~ spl9_26 ),
    inference(backward_demodulation,[],[f303,f271])).

fof(f271,plain,
    ( k4_tarski(sK3(k1_tarski(sK0),k1_tarski(sK1),sK8(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(k4_tarski(sK0,sK1)))),sK1) = sK8(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(k4_tarski(sK0,sK1)))
    | ~ spl9_26 ),
    inference(avatar_component_clause,[],[f270])).

fof(f270,plain,
    ( spl9_26
  <=> k4_tarski(sK3(k1_tarski(sK0),k1_tarski(sK1),sK8(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(k4_tarski(sK0,sK1)))),sK1) = sK8(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(k4_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f303,plain,
    ( sK0 = sK3(k1_tarski(sK0),k1_tarski(sK1),sK8(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(k4_tarski(sK0,sK1))))
    | ~ spl9_6 ),
    inference(resolution,[],[f55,f85])).

fof(f85,plain,
    ( r2_hidden(sK8(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(k4_tarski(sK0,sK1))),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)))
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl9_6
  <=> r2_hidden(sK8(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(k4_tarski(sK0,sK1))),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
      | sK3(k1_tarski(X1),X2,X0) = X1 ) ),
    inference(resolution,[],[f42,f43])).

fof(f43,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK3(X0,X1,X3),X0)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK3(X0,X1,X3),X0)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t35_zfmisc_1.p',d2_zfmisc_1)).

fof(f321,plain,
    ( spl9_3
    | ~ spl9_4
    | ~ spl9_24 ),
    inference(avatar_contradiction_clause,[],[f320])).

fof(f320,plain,
    ( $false
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_24 ),
    inference(subsumption_resolution,[],[f315,f45])).

fof(f315,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k1_tarski(k4_tarski(sK0,sK1)))
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_24 ),
    inference(backward_demodulation,[],[f309,f69])).

fof(f69,plain,
    ( ~ r2_hidden(sK8(k1_tarski(k4_tarski(sK0,sK1)),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(k4_tarski(sK0,sK1)))
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl9_3
  <=> ~ r2_hidden(sK8(k1_tarski(k4_tarski(sK0,sK1)),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(k4_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f309,plain,
    ( k4_tarski(sK0,sK1) = sK8(k1_tarski(k4_tarski(sK0,sK1)),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)))
    | ~ spl9_4
    | ~ spl9_24 ),
    inference(backward_demodulation,[],[f302,f264])).

fof(f264,plain,
    ( k4_tarski(sK3(k1_tarski(sK0),k1_tarski(sK1),sK8(k1_tarski(k4_tarski(sK0,sK1)),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)))),sK1) = sK8(k1_tarski(k4_tarski(sK0,sK1)),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)))
    | ~ spl9_24 ),
    inference(avatar_component_clause,[],[f263])).

fof(f263,plain,
    ( spl9_24
  <=> k4_tarski(sK3(k1_tarski(sK0),k1_tarski(sK1),sK8(k1_tarski(k4_tarski(sK0,sK1)),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)))),sK1) = sK8(k1_tarski(k4_tarski(sK0,sK1)),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f302,plain,
    ( sK0 = sK3(k1_tarski(sK0),k1_tarski(sK1),sK8(k1_tarski(k4_tarski(sK0,sK1)),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))))
    | ~ spl9_4 ),
    inference(resolution,[],[f55,f72])).

fof(f72,plain,
    ( r2_hidden(sK8(k1_tarski(k4_tarski(sK0,sK1)),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)))
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl9_4
  <=> r2_hidden(sK8(k1_tarski(k4_tarski(sK0,sK1)),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f272,plain,
    ( spl9_26
    | ~ spl9_6
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f236,f177,f84,f270])).

fof(f177,plain,
    ( spl9_16
  <=> k4_tarski(sK3(k1_tarski(sK0),k1_tarski(sK1),sK8(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(k4_tarski(sK0,sK1)))),sK4(k1_tarski(sK0),k1_tarski(sK1),sK8(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(k4_tarski(sK0,sK1))))) = sK8(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(k4_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f236,plain,
    ( k4_tarski(sK3(k1_tarski(sK0),k1_tarski(sK1),sK8(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(k4_tarski(sK0,sK1)))),sK1) = sK8(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(k4_tarski(sK0,sK1)))
    | ~ spl9_6
    | ~ spl9_16 ),
    inference(backward_demodulation,[],[f216,f178])).

fof(f178,plain,
    ( k4_tarski(sK3(k1_tarski(sK0),k1_tarski(sK1),sK8(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(k4_tarski(sK0,sK1)))),sK4(k1_tarski(sK0),k1_tarski(sK1),sK8(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(k4_tarski(sK0,sK1))))) = sK8(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(k4_tarski(sK0,sK1)))
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f177])).

fof(f216,plain,
    ( sK1 = sK4(k1_tarski(sK0),k1_tarski(sK1),sK8(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(k4_tarski(sK0,sK1))))
    | ~ spl9_6 ),
    inference(resolution,[],[f54,f85])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))
      | sK4(X1,k1_tarski(X2),X0) = X2 ) ),
    inference(resolution,[],[f41,f43])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK4(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK4(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f265,plain,
    ( spl9_24
    | ~ spl9_4
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f230,f170,f71,f263])).

fof(f170,plain,
    ( spl9_14
  <=> k4_tarski(sK3(k1_tarski(sK0),k1_tarski(sK1),sK8(k1_tarski(k4_tarski(sK0,sK1)),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)))),sK4(k1_tarski(sK0),k1_tarski(sK1),sK8(k1_tarski(k4_tarski(sK0,sK1)),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))))) = sK8(k1_tarski(k4_tarski(sK0,sK1)),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f230,plain,
    ( k4_tarski(sK3(k1_tarski(sK0),k1_tarski(sK1),sK8(k1_tarski(k4_tarski(sK0,sK1)),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)))),sK1) = sK8(k1_tarski(k4_tarski(sK0,sK1)),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)))
    | ~ spl9_4
    | ~ spl9_14 ),
    inference(backward_demodulation,[],[f215,f171])).

fof(f171,plain,
    ( k4_tarski(sK3(k1_tarski(sK0),k1_tarski(sK1),sK8(k1_tarski(k4_tarski(sK0,sK1)),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)))),sK4(k1_tarski(sK0),k1_tarski(sK1),sK8(k1_tarski(k4_tarski(sK0,sK1)),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))))) = sK8(k1_tarski(k4_tarski(sK0,sK1)),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)))
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f170])).

fof(f215,plain,
    ( sK1 = sK4(k1_tarski(sK0),k1_tarski(sK1),sK8(k1_tarski(k4_tarski(sK0,sK1)),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))))
    | ~ spl9_4 ),
    inference(resolution,[],[f54,f72])).

fof(f250,plain,
    ( spl9_22
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f204,f113,f248])).

fof(f248,plain,
    ( spl9_22
  <=> sK1 = sK4(k1_tarski(sK0),k1_tarski(sK1),k4_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f113,plain,
    ( spl9_10
  <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f204,plain,
    ( sK1 = sK4(k1_tarski(sK0),k1_tarski(sK1),k4_tarski(sK0,sK1))
    | ~ spl9_10 ),
    inference(resolution,[],[f54,f114])).

fof(f114,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)))
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f113])).

fof(f243,plain,
    ( spl9_20
    | ~ spl9_10
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f217,f139,f113,f241])).

fof(f241,plain,
    ( spl9_20
  <=> k4_tarski(sK0,sK1) = k4_tarski(sK3(k1_tarski(sK0),k1_tarski(sK1),k4_tarski(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f139,plain,
    ( spl9_12
  <=> k4_tarski(sK0,sK1) = k4_tarski(sK3(k1_tarski(sK0),k1_tarski(sK1),k4_tarski(sK0,sK1)),sK4(k1_tarski(sK0),k1_tarski(sK1),k4_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f217,plain,
    ( k4_tarski(sK0,sK1) = k4_tarski(sK3(k1_tarski(sK0),k1_tarski(sK1),k4_tarski(sK0,sK1)),sK1)
    | ~ spl9_10
    | ~ spl9_12 ),
    inference(backward_demodulation,[],[f204,f140])).

fof(f140,plain,
    ( k4_tarski(sK0,sK1) = k4_tarski(sK3(k1_tarski(sK0),k1_tarski(sK1),k4_tarski(sK0,sK1)),sK4(k1_tarski(sK0),k1_tarski(sK1),k4_tarski(sK0,sK1)))
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f139])).

fof(f194,plain,
    ( spl9_18
    | ~ spl9_10
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f164,f139,f113,f192])).

fof(f192,plain,
    ( spl9_18
  <=> r2_hidden(sK4(k1_tarski(sK0),k1_tarski(sK1),k4_tarski(sK0,sK1)),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f164,plain,
    ( r2_hidden(sK4(k1_tarski(sK0),k1_tarski(sK1),k4_tarski(sK0,sK1)),k1_tarski(sK1))
    | ~ spl9_10
    | ~ spl9_12 ),
    inference(resolution,[],[f154,f114])).

fof(f154,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(X5,X6))
        | r2_hidden(sK4(k1_tarski(sK0),k1_tarski(sK1),k4_tarski(sK0,sK1)),X6) )
    | ~ spl9_12 ),
    inference(superposition,[],[f36,f140])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t35_zfmisc_1.p',l54_zfmisc_1)).

fof(f179,plain,
    ( spl9_16
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f134,f84,f177])).

fof(f134,plain,
    ( k4_tarski(sK3(k1_tarski(sK0),k1_tarski(sK1),sK8(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(k4_tarski(sK0,sK1)))),sK4(k1_tarski(sK0),k1_tarski(sK1),sK8(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(k4_tarski(sK0,sK1))))) = sK8(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(k4_tarski(sK0,sK1)))
    | ~ spl9_6 ),
    inference(resolution,[],[f40,f85])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_zfmisc_1(X0,X1))
      | k4_tarski(sK3(X0,X1,X3),sK4(X0,X1,X3)) = X3 ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(sK3(X0,X1,X3),sK4(X0,X1,X3)) = X3
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f172,plain,
    ( spl9_14
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f133,f71,f170])).

fof(f133,plain,
    ( k4_tarski(sK3(k1_tarski(sK0),k1_tarski(sK1),sK8(k1_tarski(k4_tarski(sK0,sK1)),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)))),sK4(k1_tarski(sK0),k1_tarski(sK1),sK8(k1_tarski(k4_tarski(sK0,sK1)),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))))) = sK8(k1_tarski(k4_tarski(sK0,sK1)),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)))
    | ~ spl9_4 ),
    inference(resolution,[],[f40,f72])).

fof(f141,plain,
    ( spl9_12
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f127,f113,f139])).

fof(f127,plain,
    ( k4_tarski(sK0,sK1) = k4_tarski(sK3(k1_tarski(sK0),k1_tarski(sK1),k4_tarski(sK0,sK1)),sK4(k1_tarski(sK0),k1_tarski(sK1),k4_tarski(sK0,sK1)))
    | ~ spl9_10 ),
    inference(resolution,[],[f40,f114])).

fof(f122,plain,(
    spl9_11 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f120,f45])).

fof(f120,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f119,f45])).

fof(f119,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK1))
    | ~ r2_hidden(sK0,k1_tarski(sK0))
    | ~ spl9_11 ),
    inference(resolution,[],[f117,f39])).

fof(f39,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | r2_hidden(k4_tarski(X4,X5),X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | k4_tarski(X4,X5) != X3
      | r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f117,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)))
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl9_11
  <=> ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f118,plain,
    ( ~ spl9_11
    | spl9_7
    | ~ spl9_8 ),
    inference(avatar_split_clause,[],[f111,f90,f87,f116])).

fof(f87,plain,
    ( spl9_7
  <=> ~ r2_hidden(sK8(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(k4_tarski(sK0,sK1))),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f90,plain,
    ( spl9_8
  <=> r2_hidden(sK8(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(k4_tarski(sK0,sK1))),k1_tarski(k4_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f111,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)))
    | ~ spl9_7
    | ~ spl9_8 ),
    inference(backward_demodulation,[],[f109,f88])).

fof(f88,plain,
    ( ~ r2_hidden(sK8(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(k4_tarski(sK0,sK1))),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)))
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f87])).

fof(f109,plain,
    ( k4_tarski(sK0,sK1) = sK8(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(k4_tarski(sK0,sK1)))
    | ~ spl9_8 ),
    inference(resolution,[],[f91,f43])).

fof(f91,plain,
    ( r2_hidden(sK8(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(k4_tarski(sK0,sK1))),k1_tarski(k4_tarski(sK0,sK1)))
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f90])).

fof(f107,plain,
    ( spl9_8
    | spl9_1
    | spl9_7 ),
    inference(avatar_split_clause,[],[f101,f87,f50,f90])).

fof(f50,plain,
    ( spl9_1
  <=> k1_tarski(k4_tarski(sK0,sK1)) != k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f101,plain,
    ( r2_hidden(sK8(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(k4_tarski(sK0,sK1))),k1_tarski(k4_tarski(sK0,sK1)))
    | ~ spl9_1
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f97,f51])).

fof(f51,plain,
    ( k1_tarski(k4_tarski(sK0,sK1)) != k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f97,plain,
    ( r2_hidden(sK8(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(k4_tarski(sK0,sK1))),k1_tarski(k4_tarski(sK0,sK1)))
    | k1_tarski(k4_tarski(sK0,sK1)) = k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))
    | ~ spl9_7 ),
    inference(resolution,[],[f88,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X1)
      | r2_hidden(sK8(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t35_zfmisc_1.p',t2_tarski)).

fof(f100,plain,
    ( spl9_1
    | spl9_7
    | spl9_9 ),
    inference(avatar_contradiction_clause,[],[f99])).

fof(f99,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_7
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f98,f51])).

fof(f98,plain,
    ( k1_tarski(k4_tarski(sK0,sK1)) = k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))
    | ~ spl9_7
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f97,f94])).

fof(f95,plain,
    ( ~ spl9_7
    | ~ spl9_9
    | spl9_1 ),
    inference(avatar_split_clause,[],[f60,f50,f93,f87])).

fof(f60,plain,
    ( ~ r2_hidden(sK8(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(k4_tarski(sK0,sK1))),k1_tarski(k4_tarski(sK0,sK1)))
    | ~ r2_hidden(sK8(k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(k4_tarski(sK0,sK1))),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)))
    | ~ spl9_1 ),
    inference(extensionality_resolution,[],[f34,f51])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK8(X0,X1),X1)
      | ~ r2_hidden(sK8(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f81,plain,
    ( spl9_1
    | spl9_3
    | spl9_5 ),
    inference(avatar_contradiction_clause,[],[f80])).

fof(f80,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f79,f51])).

fof(f79,plain,
    ( k1_tarski(k4_tarski(sK0,sK1)) = k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f78,f69])).

fof(f78,plain,
    ( r2_hidden(sK8(k1_tarski(k4_tarski(sK0,sK1)),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(k4_tarski(sK0,sK1)))
    | k1_tarski(k4_tarski(sK0,sK1)) = k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))
    | ~ spl9_5 ),
    inference(resolution,[],[f75,f33])).

fof(f75,plain,
    ( ~ r2_hidden(sK8(k1_tarski(k4_tarski(sK0,sK1)),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)))
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl9_5
  <=> ~ r2_hidden(sK8(k1_tarski(k4_tarski(sK0,sK1)),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f76,plain,
    ( ~ spl9_3
    | ~ spl9_5
    | spl9_1 ),
    inference(avatar_split_clause,[],[f59,f50,f74,f68])).

fof(f59,plain,
    ( ~ r2_hidden(sK8(k1_tarski(k4_tarski(sK0,sK1)),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)))
    | ~ r2_hidden(sK8(k1_tarski(k4_tarski(sK0,sK1)),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(k4_tarski(sK0,sK1)))
    | ~ spl9_1 ),
    inference(extensionality_resolution,[],[f34,f51])).

fof(f52,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f19,f50])).

fof(f19,plain,(
    k1_tarski(k4_tarski(sK0,sK1)) != k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] : k1_tarski(k4_tarski(X0,X1)) != k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] : k1_tarski(k4_tarski(X0,X1)) = k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] : k1_tarski(k4_tarski(X0,X1)) = k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t35_zfmisc_1.p',t35_zfmisc_1)).
%------------------------------------------------------------------------------
