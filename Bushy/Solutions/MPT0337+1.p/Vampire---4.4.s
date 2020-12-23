%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t151_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:03 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   43 (  70 expanded)
%              Number of leaves         :   11 (  23 expanded)
%              Depth                    :   14
%              Number of atoms          :  100 ( 183 expanded)
%              Number of equality atoms :    3 (   5 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f85,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f50,f57,f81,f84])).

fof(f84,plain,
    ( spl3_5
    | ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f83])).

fof(f83,plain,
    ( $false
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f82,f56])).

fof(f56,plain,
    ( ~ r1_xboole_0(k3_tarski(sK0),k3_tarski(sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl3_5
  <=> ~ r1_xboole_0(k3_tarski(sK0),k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f82,plain,
    ( r1_xboole_0(k3_tarski(sK0),k3_tarski(sK1))
    | ~ spl3_6 ),
    inference(resolution,[],[f80,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t151_zfmisc_1.p',symmetry_r1_xboole_0)).

fof(f80,plain,
    ( r1_xboole_0(k3_tarski(sK1),k3_tarski(sK0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl3_6
  <=> r1_xboole_0(k3_tarski(sK1),k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f81,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f74,f79])).

fof(f74,plain,(
    r1_xboole_0(k3_tarski(sK1),k3_tarski(sK0)) ),
    inference(duplicate_literal_removal,[],[f72])).

fof(f72,plain,
    ( r1_xboole_0(k3_tarski(sK1),k3_tarski(sK0))
    | r1_xboole_0(k3_tarski(sK1),k3_tarski(sK0)) ),
    inference(resolution,[],[f71,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(sK2(X0,X1),X1)
      | r1_xboole_0(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | ( ~ r1_xboole_0(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_xboole_0(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_xboole_0(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_xboole_0(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_xboole_0(X2,X1) )
     => r1_xboole_0(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t151_zfmisc_1.p',t98_zfmisc_1)).

fof(f71,plain,(
    ! [X0] :
      ( r1_xboole_0(sK2(sK1,X0),k3_tarski(sK0))
      | r1_xboole_0(k3_tarski(sK1),X0) ) ),
    inference(resolution,[],[f70,f31])).

fof(f70,plain,(
    ! [X0] :
      ( r1_xboole_0(k3_tarski(sK0),sK2(sK1,X0))
      | r1_xboole_0(k3_tarski(sK1),X0) ) ),
    inference(duplicate_literal_removal,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( r1_xboole_0(k3_tarski(sK1),X0)
      | r1_xboole_0(k3_tarski(sK0),sK2(sK1,X0))
      | r1_xboole_0(k3_tarski(sK0),sK2(sK1,X0)) ) ),
    inference(resolution,[],[f67,f33])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(sK2(sK0,X0),sK2(sK1,X1))
      | r1_xboole_0(k3_tarski(sK1),X1)
      | r1_xboole_0(k3_tarski(sK0),X0) ) ),
    inference(resolution,[],[f62,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f62,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,sK0)
      | r1_xboole_0(X5,sK2(sK1,X4))
      | r1_xboole_0(k3_tarski(sK1),X4) ) ),
    inference(resolution,[],[f32,f25])).

fof(f25,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,sK1)
      | r1_xboole_0(X2,X3)
      | ~ r2_hidden(X2,sK0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ r1_xboole_0(k3_tarski(sK0),k3_tarski(sK1))
    & ! [X2,X3] :
        ( r1_xboole_0(X2,X3)
        | ~ r2_hidden(X3,sK1)
        | ~ r2_hidden(X2,sK0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( ~ r1_xboole_0(k3_tarski(X0),k3_tarski(X1))
        & ! [X2,X3] :
            ( r1_xboole_0(X2,X3)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X0) ) )
   => ( ~ r1_xboole_0(k3_tarski(sK0),k3_tarski(sK1))
      & ! [X3,X2] :
          ( r1_xboole_0(X2,X3)
          | ~ r2_hidden(X3,sK1)
          | ~ r2_hidden(X2,sK0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ~ r1_xboole_0(k3_tarski(X0),k3_tarski(X1))
      & ! [X2,X3] :
          ( r1_xboole_0(X2,X3)
          | ~ r2_hidden(X3,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ~ r1_xboole_0(k3_tarski(X0),k3_tarski(X1))
      & ! [X2,X3] :
          ( r1_xboole_0(X2,X3)
          | ~ r2_hidden(X3,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ! [X2,X3] :
            ( ( r2_hidden(X3,X1)
              & r2_hidden(X2,X0) )
           => r1_xboole_0(X2,X3) )
       => r1_xboole_0(k3_tarski(X0),k3_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( r2_hidden(X3,X1)
            & r2_hidden(X2,X0) )
         => r1_xboole_0(X2,X3) )
     => r1_xboole_0(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t151_zfmisc_1.p',t151_zfmisc_1)).

fof(f57,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f26,f55])).

fof(f26,plain,(
    ~ r1_xboole_0(k3_tarski(sK0),k3_tarski(sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f50,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f28,f48])).

fof(f48,plain,
    ( spl3_2
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f28,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t151_zfmisc_1.p',d2_xboole_0)).

fof(f43,plain,(
    spl3_0 ),
    inference(avatar_split_clause,[],[f36,f41])).

fof(f41,plain,
    ( spl3_0
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_0])])).

fof(f36,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f27,f28])).

fof(f27,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t151_zfmisc_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
