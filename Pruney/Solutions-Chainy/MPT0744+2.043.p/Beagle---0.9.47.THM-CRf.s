%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:20 EST 2020

% Result     : Theorem 25.98s
% Output     : CNFRefutation 25.98s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 202 expanded)
%              Number of leaves         :   46 (  85 expanded)
%              Depth                    :   10
%              Number of atoms          :  157 ( 383 expanded)
%              Number of equality atoms :   34 (  53 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_5 > #skF_1 > #skF_3 > #skF_7 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_45,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_93,axiom,(
    ! [A,B,C,D,E,F,G,H,I] :
      ( I = k6_enumset1(A,B,C,D,E,F,G,H)
    <=> ! [J] :
          ( r2_hidden(J,I)
        <=> ~ ( J != A
              & J != B
              & J != C
              & J != D
              & J != E
              & J != F
              & J != G
              & J != H ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_enumset1)).

tff(f_101,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_149,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_116,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_99,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_125,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_xboole_0(A,B)
           => r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_ordinal1)).

tff(f_63,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_108,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

tff(c_26,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_28,plain,(
    ! [A_10,B_11] : k1_enumset1(A_10,A_10,B_11) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_30,plain,(
    ! [A_12,B_13,C_14] : k2_enumset1(A_12,A_12,B_13,C_14) = k1_enumset1(A_12,B_13,C_14) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_32,plain,(
    ! [A_15,B_16,C_17,D_18] : k3_enumset1(A_15,A_15,B_16,C_17,D_18) = k2_enumset1(A_15,B_16,C_17,D_18) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_34,plain,(
    ! [A_19,C_21,D_22,B_20,E_23] : k4_enumset1(A_19,A_19,B_20,C_21,D_22,E_23) = k3_enumset1(A_19,B_20,C_21,D_22,E_23) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_36,plain,(
    ! [A_24,B_25,F_29,D_27,C_26,E_28] : k5_enumset1(A_24,A_24,B_25,C_26,D_27,E_28,F_29) = k4_enumset1(A_24,B_25,C_26,D_27,E_28,F_29) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2172,plain,(
    ! [E_374,F_372,B_371,A_373,G_376,D_375,C_370] : k6_enumset1(A_373,A_373,B_371,C_370,D_375,E_374,F_372,G_376) = k5_enumset1(A_373,B_371,C_370,D_375,E_374,F_372,G_376) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_50,plain,(
    ! [B_43,A_42,H_49,D_45,E_46,J_53,C_44,F_47] : r2_hidden(J_53,k6_enumset1(A_42,B_43,C_44,D_45,E_46,F_47,J_53,H_49)) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2239,plain,(
    ! [C_379,A_385,G_381,E_383,D_380,F_382,B_384] : r2_hidden(F_382,k5_enumset1(A_385,B_384,C_379,D_380,E_383,F_382,G_381)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2172,c_50])).

tff(c_2328,plain,(
    ! [C_386,D_391,A_390,E_388,B_387,F_389] : r2_hidden(E_388,k4_enumset1(A_390,B_387,C_386,D_391,E_388,F_389)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_2239])).

tff(c_2619,plain,(
    ! [B_397,D_399,A_398,E_396,C_395] : r2_hidden(D_399,k3_enumset1(A_398,B_397,C_395,D_399,E_396)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_2328])).

tff(c_2708,plain,(
    ! [C_400,A_401,B_402,D_403] : r2_hidden(C_400,k2_enumset1(A_401,B_402,C_400,D_403)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_2619])).

tff(c_2797,plain,(
    ! [B_404,A_405,C_406] : r2_hidden(B_404,k1_enumset1(A_405,B_404,C_406)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_2708])).

tff(c_2886,plain,(
    ! [A_407,B_408] : r2_hidden(A_407,k2_tarski(A_407,B_408)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2797])).

tff(c_2995,plain,(
    ! [A_409] : r2_hidden(A_409,k1_tarski(A_409)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2886])).

tff(c_104,plain,(
    ! [A_55] : k2_xboole_0(A_55,k1_tarski(A_55)) = k1_ordinal1(A_55) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_290,plain,(
    ! [D_104,B_105,A_106] :
      ( ~ r2_hidden(D_104,B_105)
      | r2_hidden(D_104,k2_xboole_0(A_106,B_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_302,plain,(
    ! [D_104,A_55] :
      ( ~ r2_hidden(D_104,k1_tarski(A_55))
      | r2_hidden(D_104,k1_ordinal1(A_55)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_290])).

tff(c_3129,plain,(
    ! [A_409] : r2_hidden(A_409,k1_ordinal1(A_409)) ),
    inference(resolution,[status(thm)],[c_2995,c_302])).

tff(c_124,plain,(
    v3_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_122,plain,(
    v3_ordinal1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_132,plain,
    ( r2_hidden('#skF_6',k1_ordinal1('#skF_7'))
    | r1_ordinal1('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_161,plain,(
    r1_ordinal1('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_132])).

tff(c_114,plain,(
    ! [A_60,B_61] :
      ( r1_tarski(A_60,B_61)
      | ~ r1_ordinal1(A_60,B_61)
      | ~ v3_ordinal1(B_61)
      | ~ v3_ordinal1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_143,plain,(
    ! [A_73] :
      ( v1_ordinal1(A_73)
      | ~ v3_ordinal1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_151,plain,(
    v1_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_124,c_143])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( r2_xboole_0(A_7,B_8)
      | B_8 = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_488,plain,(
    ! [A_142,B_143] :
      ( r2_hidden(A_142,B_143)
      | ~ r2_xboole_0(A_142,B_143)
      | ~ v3_ordinal1(B_143)
      | ~ v1_ordinal1(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_39636,plain,(
    ! [A_138768,B_138769] :
      ( r2_hidden(A_138768,B_138769)
      | ~ v3_ordinal1(B_138769)
      | ~ v1_ordinal1(A_138768)
      | B_138769 = A_138768
      | ~ r1_tarski(A_138768,B_138769) ) ),
    inference(resolution,[status(thm)],[c_20,c_488])).

tff(c_245,plain,(
    ! [D_95,A_96,B_97] :
      ( ~ r2_hidden(D_95,A_96)
      | r2_hidden(D_95,k2_xboole_0(A_96,B_97)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_260,plain,(
    ! [D_98,A_99] :
      ( ~ r2_hidden(D_98,A_99)
      | r2_hidden(D_98,k1_ordinal1(A_99)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_245])).

tff(c_126,plain,
    ( ~ r1_ordinal1('#skF_6','#skF_7')
    | ~ r2_hidden('#skF_6',k1_ordinal1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_190,plain,(
    ~ r2_hidden('#skF_6',k1_ordinal1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_126])).

tff(c_271,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_260,c_190])).

tff(c_40244,plain,
    ( ~ v3_ordinal1('#skF_7')
    | ~ v1_ordinal1('#skF_6')
    | '#skF_7' = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_39636,c_271])).

tff(c_40424,plain,
    ( '#skF_7' = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_122,c_40244])).

tff(c_40431,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_40424])).

tff(c_40437,plain,
    ( ~ r1_ordinal1('#skF_6','#skF_7')
    | ~ v3_ordinal1('#skF_7')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_114,c_40431])).

tff(c_40444,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_122,c_161,c_40437])).

tff(c_40445,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_40424])).

tff(c_40450,plain,(
    ~ r2_hidden('#skF_6',k1_ordinal1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40445,c_190])).

tff(c_40457,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3129,c_40450])).

tff(c_40459,plain,(
    ~ r1_ordinal1('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_150,plain,(
    v1_ordinal1('#skF_7') ),
    inference(resolution,[status(thm)],[c_122,c_143])).

tff(c_40458,plain,(
    r2_hidden('#skF_6',k1_ordinal1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_40460,plain,(
    ~ r2_hidden('#skF_6',k1_ordinal1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_40462,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40458,c_40460])).

tff(c_40464,plain,(
    r2_hidden('#skF_6',k1_ordinal1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_40888,plain,(
    ! [D_139887,B_139888,A_139889] :
      ( r2_hidden(D_139887,B_139888)
      | r2_hidden(D_139887,A_139889)
      | ~ r2_hidden(D_139887,k2_xboole_0(A_139889,B_139888)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_41672,plain,(
    ! [D_140029,A_140030] :
      ( r2_hidden(D_140029,k1_tarski(A_140030))
      | r2_hidden(D_140029,A_140030)
      | ~ r2_hidden(D_140029,k1_ordinal1(A_140030)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_40888])).

tff(c_44,plain,(
    ! [A_41] : k3_tarski(k1_tarski(A_41)) = A_41 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_40497,plain,(
    ! [A_139819,B_139820] :
      ( r1_tarski(A_139819,k3_tarski(B_139820))
      | ~ r2_hidden(A_139819,B_139820) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_40504,plain,(
    ! [A_139819,A_41] :
      ( r1_tarski(A_139819,A_41)
      | ~ r2_hidden(A_139819,k1_tarski(A_41)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_40497])).

tff(c_41784,plain,(
    ! [D_140031,A_140032] :
      ( r1_tarski(D_140031,A_140032)
      | r2_hidden(D_140031,A_140032)
      | ~ r2_hidden(D_140031,k1_ordinal1(A_140032)) ) ),
    inference(resolution,[status(thm)],[c_41672,c_40504])).

tff(c_41806,plain,
    ( r1_tarski('#skF_6','#skF_7')
    | r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_40464,c_41784])).

tff(c_41816,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_41806])).

tff(c_106,plain,(
    ! [B_59,A_56] :
      ( r1_tarski(B_59,A_56)
      | ~ r2_hidden(B_59,A_56)
      | ~ v1_ordinal1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_41819,plain,
    ( r1_tarski('#skF_6','#skF_7')
    | ~ v1_ordinal1('#skF_7') ),
    inference(resolution,[status(thm)],[c_41816,c_106])).

tff(c_41825,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_41819])).

tff(c_112,plain,(
    ! [A_60,B_61] :
      ( r1_ordinal1(A_60,B_61)
      | ~ r1_tarski(A_60,B_61)
      | ~ v3_ordinal1(B_61)
      | ~ v3_ordinal1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_41829,plain,
    ( r1_ordinal1('#skF_6','#skF_7')
    | ~ v3_ordinal1('#skF_7')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_41825,c_112])).

tff(c_41832,plain,(
    r1_ordinal1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_122,c_41829])).

tff(c_41834,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40459,c_41832])).

tff(c_41835,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_41806])).

tff(c_41839,plain,
    ( r1_ordinal1('#skF_6','#skF_7')
    | ~ v3_ordinal1('#skF_7')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_41835,c_112])).

tff(c_41842,plain,(
    r1_ordinal1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_122,c_41839])).

tff(c_41844,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40459,c_41842])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:37:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 25.98/16.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.98/16.62  
% 25.98/16.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.98/16.63  %$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_5 > #skF_1 > #skF_3 > #skF_7 > #skF_6 > #skF_2 > #skF_4
% 25.98/16.63  
% 25.98/16.63  %Foreground sorts:
% 25.98/16.63  
% 25.98/16.63  
% 25.98/16.63  %Background operators:
% 25.98/16.63  
% 25.98/16.63  
% 25.98/16.63  %Foreground operators:
% 25.98/16.63  tff('#skF_5', type, '#skF_5': $i > $i).
% 25.98/16.63  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 25.98/16.63  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 25.98/16.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 25.98/16.63  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 25.98/16.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 25.98/16.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 25.98/16.63  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 25.98/16.63  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 25.98/16.63  tff('#skF_7', type, '#skF_7': $i).
% 25.98/16.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 25.98/16.63  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 25.98/16.63  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 25.98/16.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 25.98/16.63  tff('#skF_6', type, '#skF_6': $i).
% 25.98/16.63  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 25.98/16.63  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 25.98/16.63  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 25.98/16.63  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 25.98/16.63  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 25.98/16.63  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 25.98/16.63  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 25.98/16.63  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 25.98/16.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 25.98/16.63  tff(k3_tarski, type, k3_tarski: $i > $i).
% 25.98/16.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 25.98/16.63  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 25.98/16.63  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 25.98/16.63  
% 25.98/16.65  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 25.98/16.65  tff(f_45, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 25.98/16.65  tff(f_47, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 25.98/16.65  tff(f_49, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 25.98/16.65  tff(f_51, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 25.98/16.65  tff(f_53, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 25.98/16.65  tff(f_55, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 25.98/16.65  tff(f_93, axiom, (![A, B, C, D, E, F, G, H, I]: ((I = k6_enumset1(A, B, C, D, E, F, G, H)) <=> (![J]: (r2_hidden(J, I) <=> ~(((((((~(J = A) & ~(J = B)) & ~(J = C)) & ~(J = D)) & ~(J = E)) & ~(J = F)) & ~(J = G)) & ~(J = H)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_enumset1)).
% 25.98/16.65  tff(f_101, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 25.98/16.65  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 25.98/16.65  tff(f_149, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_ordinal1)).
% 25.98/16.65  tff(f_116, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 25.98/16.65  tff(f_99, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_ordinal1)).
% 25.98/16.65  tff(f_41, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 25.98/16.65  tff(f_125, axiom, (![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_xboole_0(A, B) => r2_hidden(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_ordinal1)).
% 25.98/16.65  tff(f_63, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 25.98/16.65  tff(f_59, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 25.98/16.65  tff(f_108, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_ordinal1)).
% 25.98/16.65  tff(c_26, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 25.98/16.65  tff(c_28, plain, (![A_10, B_11]: (k1_enumset1(A_10, A_10, B_11)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 25.98/16.65  tff(c_30, plain, (![A_12, B_13, C_14]: (k2_enumset1(A_12, A_12, B_13, C_14)=k1_enumset1(A_12, B_13, C_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 25.98/16.65  tff(c_32, plain, (![A_15, B_16, C_17, D_18]: (k3_enumset1(A_15, A_15, B_16, C_17, D_18)=k2_enumset1(A_15, B_16, C_17, D_18))), inference(cnfTransformation, [status(thm)], [f_49])).
% 25.98/16.65  tff(c_34, plain, (![A_19, C_21, D_22, B_20, E_23]: (k4_enumset1(A_19, A_19, B_20, C_21, D_22, E_23)=k3_enumset1(A_19, B_20, C_21, D_22, E_23))), inference(cnfTransformation, [status(thm)], [f_51])).
% 25.98/16.65  tff(c_36, plain, (![A_24, B_25, F_29, D_27, C_26, E_28]: (k5_enumset1(A_24, A_24, B_25, C_26, D_27, E_28, F_29)=k4_enumset1(A_24, B_25, C_26, D_27, E_28, F_29))), inference(cnfTransformation, [status(thm)], [f_53])).
% 25.98/16.65  tff(c_2172, plain, (![E_374, F_372, B_371, A_373, G_376, D_375, C_370]: (k6_enumset1(A_373, A_373, B_371, C_370, D_375, E_374, F_372, G_376)=k5_enumset1(A_373, B_371, C_370, D_375, E_374, F_372, G_376))), inference(cnfTransformation, [status(thm)], [f_55])).
% 25.98/16.65  tff(c_50, plain, (![B_43, A_42, H_49, D_45, E_46, J_53, C_44, F_47]: (r2_hidden(J_53, k6_enumset1(A_42, B_43, C_44, D_45, E_46, F_47, J_53, H_49)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 25.98/16.65  tff(c_2239, plain, (![C_379, A_385, G_381, E_383, D_380, F_382, B_384]: (r2_hidden(F_382, k5_enumset1(A_385, B_384, C_379, D_380, E_383, F_382, G_381)))), inference(superposition, [status(thm), theory('equality')], [c_2172, c_50])).
% 25.98/16.65  tff(c_2328, plain, (![C_386, D_391, A_390, E_388, B_387, F_389]: (r2_hidden(E_388, k4_enumset1(A_390, B_387, C_386, D_391, E_388, F_389)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_2239])).
% 25.98/16.65  tff(c_2619, plain, (![B_397, D_399, A_398, E_396, C_395]: (r2_hidden(D_399, k3_enumset1(A_398, B_397, C_395, D_399, E_396)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_2328])).
% 25.98/16.65  tff(c_2708, plain, (![C_400, A_401, B_402, D_403]: (r2_hidden(C_400, k2_enumset1(A_401, B_402, C_400, D_403)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_2619])).
% 25.98/16.65  tff(c_2797, plain, (![B_404, A_405, C_406]: (r2_hidden(B_404, k1_enumset1(A_405, B_404, C_406)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_2708])).
% 25.98/16.65  tff(c_2886, plain, (![A_407, B_408]: (r2_hidden(A_407, k2_tarski(A_407, B_408)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_2797])).
% 25.98/16.65  tff(c_2995, plain, (![A_409]: (r2_hidden(A_409, k1_tarski(A_409)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_2886])).
% 25.98/16.65  tff(c_104, plain, (![A_55]: (k2_xboole_0(A_55, k1_tarski(A_55))=k1_ordinal1(A_55))), inference(cnfTransformation, [status(thm)], [f_101])).
% 25.98/16.65  tff(c_290, plain, (![D_104, B_105, A_106]: (~r2_hidden(D_104, B_105) | r2_hidden(D_104, k2_xboole_0(A_106, B_105)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 25.98/16.65  tff(c_302, plain, (![D_104, A_55]: (~r2_hidden(D_104, k1_tarski(A_55)) | r2_hidden(D_104, k1_ordinal1(A_55)))), inference(superposition, [status(thm), theory('equality')], [c_104, c_290])).
% 25.98/16.65  tff(c_3129, plain, (![A_409]: (r2_hidden(A_409, k1_ordinal1(A_409)))), inference(resolution, [status(thm)], [c_2995, c_302])).
% 25.98/16.65  tff(c_124, plain, (v3_ordinal1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_149])).
% 25.98/16.65  tff(c_122, plain, (v3_ordinal1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_149])).
% 25.98/16.65  tff(c_132, plain, (r2_hidden('#skF_6', k1_ordinal1('#skF_7')) | r1_ordinal1('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_149])).
% 25.98/16.65  tff(c_161, plain, (r1_ordinal1('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_132])).
% 25.98/16.65  tff(c_114, plain, (![A_60, B_61]: (r1_tarski(A_60, B_61) | ~r1_ordinal1(A_60, B_61) | ~v3_ordinal1(B_61) | ~v3_ordinal1(A_60))), inference(cnfTransformation, [status(thm)], [f_116])).
% 25.98/16.65  tff(c_143, plain, (![A_73]: (v1_ordinal1(A_73) | ~v3_ordinal1(A_73))), inference(cnfTransformation, [status(thm)], [f_99])).
% 25.98/16.65  tff(c_151, plain, (v1_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_124, c_143])).
% 25.98/16.65  tff(c_20, plain, (![A_7, B_8]: (r2_xboole_0(A_7, B_8) | B_8=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 25.98/16.65  tff(c_488, plain, (![A_142, B_143]: (r2_hidden(A_142, B_143) | ~r2_xboole_0(A_142, B_143) | ~v3_ordinal1(B_143) | ~v1_ordinal1(A_142))), inference(cnfTransformation, [status(thm)], [f_125])).
% 25.98/16.65  tff(c_39636, plain, (![A_138768, B_138769]: (r2_hidden(A_138768, B_138769) | ~v3_ordinal1(B_138769) | ~v1_ordinal1(A_138768) | B_138769=A_138768 | ~r1_tarski(A_138768, B_138769))), inference(resolution, [status(thm)], [c_20, c_488])).
% 25.98/16.65  tff(c_245, plain, (![D_95, A_96, B_97]: (~r2_hidden(D_95, A_96) | r2_hidden(D_95, k2_xboole_0(A_96, B_97)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 25.98/16.65  tff(c_260, plain, (![D_98, A_99]: (~r2_hidden(D_98, A_99) | r2_hidden(D_98, k1_ordinal1(A_99)))), inference(superposition, [status(thm), theory('equality')], [c_104, c_245])).
% 25.98/16.65  tff(c_126, plain, (~r1_ordinal1('#skF_6', '#skF_7') | ~r2_hidden('#skF_6', k1_ordinal1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 25.98/16.65  tff(c_190, plain, (~r2_hidden('#skF_6', k1_ordinal1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_126])).
% 25.98/16.65  tff(c_271, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_260, c_190])).
% 25.98/16.65  tff(c_40244, plain, (~v3_ordinal1('#skF_7') | ~v1_ordinal1('#skF_6') | '#skF_7'='#skF_6' | ~r1_tarski('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_39636, c_271])).
% 25.98/16.65  tff(c_40424, plain, ('#skF_7'='#skF_6' | ~r1_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_151, c_122, c_40244])).
% 25.98/16.65  tff(c_40431, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_40424])).
% 25.98/16.65  tff(c_40437, plain, (~r1_ordinal1('#skF_6', '#skF_7') | ~v3_ordinal1('#skF_7') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_114, c_40431])).
% 25.98/16.65  tff(c_40444, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_124, c_122, c_161, c_40437])).
% 25.98/16.65  tff(c_40445, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_40424])).
% 25.98/16.65  tff(c_40450, plain, (~r2_hidden('#skF_6', k1_ordinal1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_40445, c_190])).
% 25.98/16.65  tff(c_40457, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3129, c_40450])).
% 25.98/16.65  tff(c_40459, plain, (~r1_ordinal1('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_132])).
% 25.98/16.65  tff(c_150, plain, (v1_ordinal1('#skF_7')), inference(resolution, [status(thm)], [c_122, c_143])).
% 25.98/16.65  tff(c_40458, plain, (r2_hidden('#skF_6', k1_ordinal1('#skF_7'))), inference(splitRight, [status(thm)], [c_132])).
% 25.98/16.65  tff(c_40460, plain, (~r2_hidden('#skF_6', k1_ordinal1('#skF_7'))), inference(splitLeft, [status(thm)], [c_126])).
% 25.98/16.65  tff(c_40462, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40458, c_40460])).
% 25.98/16.65  tff(c_40464, plain, (r2_hidden('#skF_6', k1_ordinal1('#skF_7'))), inference(splitRight, [status(thm)], [c_126])).
% 25.98/16.65  tff(c_40888, plain, (![D_139887, B_139888, A_139889]: (r2_hidden(D_139887, B_139888) | r2_hidden(D_139887, A_139889) | ~r2_hidden(D_139887, k2_xboole_0(A_139889, B_139888)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 25.98/16.65  tff(c_41672, plain, (![D_140029, A_140030]: (r2_hidden(D_140029, k1_tarski(A_140030)) | r2_hidden(D_140029, A_140030) | ~r2_hidden(D_140029, k1_ordinal1(A_140030)))), inference(superposition, [status(thm), theory('equality')], [c_104, c_40888])).
% 25.98/16.65  tff(c_44, plain, (![A_41]: (k3_tarski(k1_tarski(A_41))=A_41)), inference(cnfTransformation, [status(thm)], [f_63])).
% 25.98/16.65  tff(c_40497, plain, (![A_139819, B_139820]: (r1_tarski(A_139819, k3_tarski(B_139820)) | ~r2_hidden(A_139819, B_139820))), inference(cnfTransformation, [status(thm)], [f_59])).
% 25.98/16.65  tff(c_40504, plain, (![A_139819, A_41]: (r1_tarski(A_139819, A_41) | ~r2_hidden(A_139819, k1_tarski(A_41)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_40497])).
% 25.98/16.65  tff(c_41784, plain, (![D_140031, A_140032]: (r1_tarski(D_140031, A_140032) | r2_hidden(D_140031, A_140032) | ~r2_hidden(D_140031, k1_ordinal1(A_140032)))), inference(resolution, [status(thm)], [c_41672, c_40504])).
% 25.98/16.65  tff(c_41806, plain, (r1_tarski('#skF_6', '#skF_7') | r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_40464, c_41784])).
% 25.98/16.65  tff(c_41816, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_41806])).
% 25.98/16.65  tff(c_106, plain, (![B_59, A_56]: (r1_tarski(B_59, A_56) | ~r2_hidden(B_59, A_56) | ~v1_ordinal1(A_56))), inference(cnfTransformation, [status(thm)], [f_108])).
% 25.98/16.65  tff(c_41819, plain, (r1_tarski('#skF_6', '#skF_7') | ~v1_ordinal1('#skF_7')), inference(resolution, [status(thm)], [c_41816, c_106])).
% 25.98/16.65  tff(c_41825, plain, (r1_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_150, c_41819])).
% 25.98/16.65  tff(c_112, plain, (![A_60, B_61]: (r1_ordinal1(A_60, B_61) | ~r1_tarski(A_60, B_61) | ~v3_ordinal1(B_61) | ~v3_ordinal1(A_60))), inference(cnfTransformation, [status(thm)], [f_116])).
% 25.98/16.65  tff(c_41829, plain, (r1_ordinal1('#skF_6', '#skF_7') | ~v3_ordinal1('#skF_7') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_41825, c_112])).
% 25.98/16.65  tff(c_41832, plain, (r1_ordinal1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_122, c_41829])).
% 25.98/16.65  tff(c_41834, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40459, c_41832])).
% 25.98/16.65  tff(c_41835, plain, (r1_tarski('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_41806])).
% 25.98/16.65  tff(c_41839, plain, (r1_ordinal1('#skF_6', '#skF_7') | ~v3_ordinal1('#skF_7') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_41835, c_112])).
% 25.98/16.65  tff(c_41842, plain, (r1_ordinal1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_122, c_41839])).
% 25.98/16.65  tff(c_41844, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40459, c_41842])).
% 25.98/16.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.98/16.65  
% 25.98/16.65  Inference rules
% 25.98/16.65  ----------------------
% 25.98/16.65  #Ref     : 0
% 25.98/16.65  #Sup     : 7703
% 25.98/16.65  #Fact    : 454
% 25.98/16.65  #Define  : 0
% 25.98/16.65  #Split   : 7
% 25.98/16.65  #Chain   : 0
% 25.98/16.65  #Close   : 0
% 25.98/16.65  
% 25.98/16.65  Ordering : KBO
% 25.98/16.65  
% 25.98/16.65  Simplification rules
% 25.98/16.65  ----------------------
% 25.98/16.65  #Subsume      : 4315
% 25.98/16.65  #Demod        : 144
% 25.98/16.65  #Tautology    : 664
% 25.98/16.65  #SimpNegUnit  : 22
% 25.98/16.65  #BackRed      : 8
% 25.98/16.65  
% 25.98/16.65  #Partial instantiations: 38448
% 25.98/16.65  #Strategies tried      : 1
% 25.98/16.65  
% 25.98/16.65  Timing (in seconds)
% 25.98/16.65  ----------------------
% 25.98/16.65  Preprocessing        : 0.38
% 25.98/16.65  Parsing              : 0.18
% 25.98/16.65  CNF conversion       : 0.03
% 25.98/16.65  Main loop            : 15.50
% 25.98/16.65  Inferencing          : 5.59
% 25.98/16.65  Reduction            : 1.88
% 25.98/16.65  Demodulation         : 1.42
% 25.98/16.65  BG Simplification    : 0.31
% 25.98/16.65  Subsumption          : 7.45
% 25.98/16.65  Abstraction          : 1.20
% 25.98/16.65  MUC search           : 0.00
% 25.98/16.65  Cooper               : 0.00
% 25.98/16.65  Total                : 15.92
% 25.98/16.65  Index Insertion      : 0.00
% 25.98/16.65  Index Deletion       : 0.00
% 25.98/16.65  Index Matching       : 0.00
% 25.98/16.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
