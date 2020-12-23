%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1103+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:07 EST 2020

% Result     : Theorem 2.37s
% Output     : Refutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 535 expanded)
%              Number of leaves         :   18 ( 180 expanded)
%              Depth                    :   16
%              Number of atoms          :  211 (2164 expanded)
%              Number of equality atoms :   99 (1372 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4882,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3594,f3600,f3925,f4873,f4881])).

fof(f4881,plain,
    ( ~ spl96_1
    | spl96_2 ),
    inference(avatar_contradiction_clause,[],[f4880])).

fof(f4880,plain,
    ( $false
    | ~ spl96_1
    | spl96_2 ),
    inference(subsumption_resolution,[],[f3592,f4688])).

fof(f4688,plain,
    ( k2_struct_0(sK5) = sK6
    | ~ spl96_1 ),
    inference(backward_demodulation,[],[f3602,f4685])).

fof(f4685,plain,
    ( u1_struct_0(sK5) = sK6
    | ~ spl96_1 ),
    inference(forward_demodulation,[],[f4656,f4171])).

fof(f4171,plain,(
    sK6 = k4_subset_1(u1_struct_0(sK5),sK6,k1_xboole_0) ),
    inference(forward_demodulation,[],[f3981,f2578])).

fof(f2578,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f76])).

fof(f76,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f3981,plain,(
    k2_xboole_0(sK6,k1_xboole_0) = k4_subset_1(u1_struct_0(sK5),sK6,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f2580,f2503,f2782])).

fof(f2782,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f1932])).

fof(f1932,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f1931])).

fof(f1931,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f491])).

fof(f491,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f2503,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f2235])).

fof(f2235,plain,
    ( ( ( k2_struct_0(sK5) = sK6
        & k1_xboole_0 != k7_subset_1(u1_struct_0(sK5),k2_struct_0(sK5),sK6) )
      | ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK5),k2_struct_0(sK5),sK6)
        & k2_struct_0(sK5) != sK6 ) )
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    & l1_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f1784,f2234,f2233])).

fof(f2233,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ( k2_struct_0(X0) = X1
                & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
              | ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
                & k2_struct_0(X0) != X1 ) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ( ( k2_struct_0(sK5) = X1
              & k1_xboole_0 != k7_subset_1(u1_struct_0(sK5),k2_struct_0(sK5),X1) )
            | ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK5),k2_struct_0(sK5),X1)
              & k2_struct_0(sK5) != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) )
      & l1_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f2234,plain,
    ( ? [X1] :
        ( ( ( k2_struct_0(sK5) = X1
            & k1_xboole_0 != k7_subset_1(u1_struct_0(sK5),k2_struct_0(sK5),X1) )
          | ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK5),k2_struct_0(sK5),X1)
            & k2_struct_0(sK5) != X1 ) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) )
   => ( ( ( k2_struct_0(sK5) = sK6
          & k1_xboole_0 != k7_subset_1(u1_struct_0(sK5),k2_struct_0(sK5),sK6) )
        | ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK5),k2_struct_0(sK5),sK6)
          & k2_struct_0(sK5) != sK6 ) )
      & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ) ),
    introduced(choice_axiom,[])).

fof(f1784,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( k2_struct_0(X0) = X1
              & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
            | ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
              & k2_struct_0(X0) != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1773])).

fof(f1773,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ~ ( k2_struct_0(X0) = X1
                  & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
              & ~ ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
                  & k2_struct_0(X0) != X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f1772])).

fof(f1772,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ~ ( k2_struct_0(X0) = X1
                & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
            & ~ ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
                & k2_struct_0(X0) != X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_pre_topc)).

fof(f2580,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f522])).

fof(f522,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f4656,plain,
    ( u1_struct_0(sK5) = k4_subset_1(u1_struct_0(sK5),sK6,k1_xboole_0)
    | ~ spl96_1 ),
    inference(backward_demodulation,[],[f4109,f4647])).

fof(f4647,plain,
    ( k1_xboole_0 = k4_xboole_0(u1_struct_0(sK5),sK6)
    | ~ spl96_1 ),
    inference(subsumption_resolution,[],[f4630,f3928])).

fof(f3928,plain,(
    m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(forward_demodulation,[],[f3603,f3602])).

fof(f3603,plain,(
    m1_subset_1(k2_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(unit_resulting_resolution,[],[f2502,f2585])).

fof(f2585,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f1826])).

fof(f1826,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1761])).

fof(f1761,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f2502,plain,(
    l1_struct_0(sK5) ),
    inference(cnf_transformation,[],[f2235])).

fof(f4630,plain,
    ( k1_xboole_0 = k4_xboole_0(u1_struct_0(sK5),sK6)
    | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ spl96_1 ),
    inference(superposition,[],[f3939,f2508])).

fof(f2508,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f1785])).

fof(f1785,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f494])).

fof(f494,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f3939,plain,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK5),u1_struct_0(sK5),sK6)
    | ~ spl96_1 ),
    inference(forward_demodulation,[],[f3589,f3602])).

fof(f3589,plain,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK5),k2_struct_0(sK5),sK6)
    | ~ spl96_1 ),
    inference(avatar_component_clause,[],[f3587])).

fof(f3587,plain,
    ( spl96_1
  <=> k1_xboole_0 = k7_subset_1(u1_struct_0(sK5),k2_struct_0(sK5),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl96_1])])).

fof(f4109,plain,(
    u1_struct_0(sK5) = k4_subset_1(u1_struct_0(sK5),sK6,k4_xboole_0(u1_struct_0(sK5),sK6)) ),
    inference(backward_demodulation,[],[f4069,f4031])).

fof(f4031,plain,(
    k3_subset_1(u1_struct_0(sK5),sK6) = k4_xboole_0(u1_struct_0(sK5),sK6) ),
    inference(unit_resulting_resolution,[],[f2503,f2814])).

fof(f2814,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f1964])).

fof(f1964,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f462])).

fof(f462,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f4069,plain,(
    u1_struct_0(sK5) = k4_subset_1(u1_struct_0(sK5),sK6,k3_subset_1(u1_struct_0(sK5),sK6)) ),
    inference(forward_demodulation,[],[f4060,f3347])).

fof(f3347,plain,(
    ! [X0] : k3_subset_1(X0,k1_subset_1(X0)) = X0 ),
    inference(definition_unfolding,[],[f2765,f2763])).

fof(f2763,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f502])).

fof(f502,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(f2765,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f460])).

fof(f460,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f4060,plain,(
    k3_subset_1(u1_struct_0(sK5),k1_subset_1(u1_struct_0(sK5))) = k4_subset_1(u1_struct_0(sK5),sK6,k3_subset_1(u1_struct_0(sK5),sK6)) ),
    inference(unit_resulting_resolution,[],[f2503,f3344])).

fof(f3344,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k1_subset_1(X0)) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f2761,f2763])).

fof(f2761,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f1918])).

fof(f1918,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f503])).

fof(f503,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

fof(f3602,plain,(
    k2_struct_0(sK5) = u1_struct_0(sK5) ),
    inference(unit_resulting_resolution,[],[f2502,f2586])).

fof(f2586,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f1827])).

fof(f1827,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1760])).

fof(f1760,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f3592,plain,
    ( k2_struct_0(sK5) != sK6
    | spl96_2 ),
    inference(avatar_component_clause,[],[f3591])).

fof(f3591,plain,
    ( spl96_2
  <=> k2_struct_0(sK5) = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl96_2])])).

fof(f4873,plain,
    ( ~ spl96_1
    | spl96_3 ),
    inference(avatar_contradiction_clause,[],[f4872])).

fof(f4872,plain,
    ( $false
    | ~ spl96_1
    | spl96_3 ),
    inference(subsumption_resolution,[],[f4871,f4686])).

fof(f4686,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK6))
    | ~ spl96_1 ),
    inference(backward_demodulation,[],[f2503,f4685])).

fof(f4871,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(sK6))
    | ~ spl96_1
    | spl96_3 ),
    inference(forward_demodulation,[],[f4870,f4685])).

fof(f4870,plain,
    ( ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ spl96_1
    | spl96_3 ),
    inference(subsumption_resolution,[],[f4869,f4625])).

fof(f4625,plain,
    ( k1_xboole_0 != k4_xboole_0(sK6,sK6)
    | spl96_3 ),
    inference(subsumption_resolution,[],[f4391,f2503])).

fof(f4391,plain,
    ( k1_xboole_0 != k4_xboole_0(sK6,sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | spl96_3 ),
    inference(superposition,[],[f3599,f2508])).

fof(f3599,plain,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK5),sK6,sK6)
    | spl96_3 ),
    inference(avatar_component_clause,[],[f3597])).

fof(f3597,plain,
    ( spl96_3
  <=> k1_xboole_0 = k7_subset_1(u1_struct_0(sK5),sK6,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl96_3])])).

fof(f4869,plain,
    ( k1_xboole_0 = k4_xboole_0(sK6,sK6)
    | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ spl96_1 ),
    inference(forward_demodulation,[],[f4636,f4685])).

fof(f4636,plain,
    ( k1_xboole_0 = k4_xboole_0(u1_struct_0(sK5),sK6)
    | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ spl96_1 ),
    inference(superposition,[],[f2508,f3939])).

fof(f3925,plain,
    ( ~ spl96_2
    | spl96_3 ),
    inference(avatar_contradiction_clause,[],[f3924])).

fof(f3924,plain,
    ( $false
    | ~ spl96_2
    | spl96_3 ),
    inference(subsumption_resolution,[],[f3923,f3629])).

fof(f3629,plain,
    ( k1_xboole_0 != k7_subset_1(sK6,sK6,sK6)
    | ~ spl96_2
    | spl96_3 ),
    inference(backward_demodulation,[],[f3599,f3627])).

fof(f3627,plain,
    ( u1_struct_0(sK5) = sK6
    | ~ spl96_2 ),
    inference(forward_demodulation,[],[f3602,f3593])).

fof(f3593,plain,
    ( k2_struct_0(sK5) = sK6
    | ~ spl96_2 ),
    inference(avatar_component_clause,[],[f3591])).

fof(f3923,plain,
    ( k1_xboole_0 = k7_subset_1(sK6,sK6,sK6)
    | ~ spl96_2 ),
    inference(forward_demodulation,[],[f3906,f2725])).

fof(f2725,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f100])).

fof(f100,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f3906,plain,
    ( k1_xboole_0 = k7_subset_1(sK6,sK6,k4_xboole_0(sK6,k1_xboole_0))
    | ~ spl96_2 ),
    inference(backward_demodulation,[],[f3634,f3654])).

fof(f3654,plain,
    ( ! [X0] : k7_subset_1(sK6,sK6,X0) = k4_xboole_0(sK6,X0)
    | ~ spl96_2 ),
    inference(unit_resulting_resolution,[],[f3628,f2508])).

fof(f3628,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK6))
    | ~ spl96_2 ),
    inference(backward_demodulation,[],[f2503,f3627])).

fof(f3634,plain,
    ( k1_xboole_0 = k7_subset_1(sK6,sK6,k7_subset_1(sK6,sK6,k1_xboole_0))
    | ~ spl96_2 ),
    inference(backward_demodulation,[],[f3619,f3627])).

fof(f3619,plain,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK5),sK6,k7_subset_1(u1_struct_0(sK5),sK6,k1_xboole_0))
    | ~ spl96_2 ),
    inference(forward_demodulation,[],[f3609,f3593])).

fof(f3609,plain,(
    k1_xboole_0 = k7_subset_1(u1_struct_0(sK5),k2_struct_0(sK5),k7_subset_1(u1_struct_0(sK5),k2_struct_0(sK5),k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f2580,f2502,f2518])).

fof(f2518,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f1795])).

fof(f1795,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1771])).

fof(f1771,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_pre_topc)).

fof(f3600,plain,
    ( ~ spl96_2
    | ~ spl96_3 ),
    inference(avatar_split_clause,[],[f3595,f3597,f3591])).

fof(f3595,plain,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK5),sK6,sK6)
    | k2_struct_0(sK5) != sK6 ),
    inference(inner_rewriting,[],[f2504])).

fof(f2504,plain,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK5),k2_struct_0(sK5),sK6)
    | k2_struct_0(sK5) != sK6 ),
    inference(cnf_transformation,[],[f2235])).

fof(f3594,plain,
    ( spl96_1
    | spl96_2 ),
    inference(avatar_split_clause,[],[f2507,f3591,f3587])).

fof(f2507,plain,
    ( k2_struct_0(sK5) = sK6
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK5),k2_struct_0(sK5),sK6) ),
    inference(cnf_transformation,[],[f2235])).
%------------------------------------------------------------------------------
