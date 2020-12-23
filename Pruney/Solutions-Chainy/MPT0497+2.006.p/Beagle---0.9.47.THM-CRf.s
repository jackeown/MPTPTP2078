%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:40 EST 2020

% Result     : Theorem 4.57s
% Output     : CNFRefutation 4.57s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 232 expanded)
%              Number of leaves         :   28 (  86 expanded)
%              Depth                    :   14
%              Number of atoms          :  124 ( 338 expanded)
%              Number of equality atoms :   65 ( 185 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_43,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_40,plain,
    ( k7_relat_1('#skF_3','#skF_2') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_141,plain,(
    r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_34,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2')
    | k7_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_169,plain,(
    k7_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_34])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_577,plain,(
    ! [B_65,A_66] :
      ( k3_xboole_0(k1_relat_1(B_65),A_66) = k1_relat_1(k7_relat_1(B_65,A_66))
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1960,plain,(
    ! [B_105,B_106] :
      ( k3_xboole_0(B_105,k1_relat_1(B_106)) = k1_relat_1(k7_relat_1(B_106,B_105))
      | ~ v1_relat_1(B_106) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_577])).

tff(c_8,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_194,plain,(
    ! [A_42,B_43] : k4_xboole_0(A_42,k4_xboole_0(A_42,B_43)) = k3_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_212,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k3_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_194])).

tff(c_216,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_212])).

tff(c_163,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(A_34,B_35) = A_34
      | ~ r1_xboole_0(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_167,plain,(
    k4_xboole_0(k1_relat_1('#skF_3'),'#skF_2') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_141,c_163])).

tff(c_209,plain,(
    k4_xboole_0(k1_relat_1('#skF_3'),k1_relat_1('#skF_3')) = k3_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_194])).

tff(c_215,plain,(
    k4_xboole_0(k1_relat_1('#skF_3'),k1_relat_1('#skF_3')) = k3_xboole_0('#skF_2',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_209])).

tff(c_270,plain,(
    k3_xboole_0('#skF_2',k1_relat_1('#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_215])).

tff(c_2025,plain,
    ( k1_relat_1(k7_relat_1('#skF_3','#skF_2')) = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1960,c_270])).

tff(c_2093,plain,(
    k1_relat_1(k7_relat_1('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2025])).

tff(c_22,plain,(
    ! [A_17,B_18] :
      ( v1_relat_1(k7_relat_1(A_17,B_18))
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_628,plain,(
    ! [B_2,B_65] :
      ( k3_xboole_0(B_2,k1_relat_1(B_65)) = k1_relat_1(k7_relat_1(B_65,B_2))
      | ~ v1_relat_1(B_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_577])).

tff(c_2101,plain,(
    ! [B_2] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_3','#skF_2'),B_2)) = k3_xboole_0(B_2,k1_xboole_0)
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2093,c_628])).

tff(c_2110,plain,(
    ! [B_2] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_3','#skF_2'),B_2)) = k1_xboole_0
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2101])).

tff(c_2116,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2110])).

tff(c_2119,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_2116])).

tff(c_2123,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2119])).

tff(c_2125,plain,(
    v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2110])).

tff(c_26,plain,(
    ! [A_19] :
      ( k1_relat_1(A_19) != k1_xboole_0
      | k1_xboole_0 = A_19
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2128,plain,
    ( k1_relat_1(k7_relat_1('#skF_3','#skF_2')) != k1_xboole_0
    | k7_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2125,c_26])).

tff(c_2134,plain,(
    k7_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2093,c_2128])).

tff(c_2136,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_169,c_2134])).

tff(c_2137,plain,(
    k7_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_2449,plain,(
    ! [B_134,A_135] :
      ( k3_xboole_0(k1_relat_1(B_134),A_135) = k1_relat_1(k7_relat_1(B_134,A_135))
      | ~ v1_relat_1(B_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_3088,plain,(
    ! [A_163,B_164] :
      ( k3_xboole_0(A_163,k1_relat_1(B_164)) = k1_relat_1(k7_relat_1(B_164,A_163))
      | ~ v1_relat_1(B_164) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2449,c_2])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),k3_xboole_0(A_3,B_4))
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2297,plain,(
    ! [A_124,B_125] : k4_xboole_0(A_124,k4_xboole_0(A_124,B_125)) = k3_xboole_0(A_124,B_125) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2326,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k3_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_2297])).

tff(c_2335,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2326])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( r1_xboole_0(A_15,B_16)
      | k4_xboole_0(A_15,B_16) != A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2367,plain,(
    ! [A_130] : k4_xboole_0(A_130,A_130) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2326])).

tff(c_16,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2372,plain,(
    ! [A_130] : k4_xboole_0(A_130,k1_xboole_0) = k3_xboole_0(A_130,A_130) ),
    inference(superposition,[status(thm),theory(equality)],[c_2367,c_16])).

tff(c_2396,plain,(
    ! [A_131] : k3_xboole_0(A_131,A_131) = A_131 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_2372])).

tff(c_6,plain,(
    ! [A_3,B_4,C_7] :
      ( ~ r1_xboole_0(A_3,B_4)
      | ~ r2_hidden(C_7,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2435,plain,(
    ! [A_132,C_133] :
      ( ~ r1_xboole_0(A_132,A_132)
      | ~ r2_hidden(C_133,A_132) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2396,c_6])).

tff(c_2444,plain,(
    ! [C_133,B_16] :
      ( ~ r2_hidden(C_133,B_16)
      | k4_xboole_0(B_16,B_16) != B_16 ) ),
    inference(resolution,[status(thm)],[c_20,c_2435])).

tff(c_2502,plain,(
    ! [C_136,B_137] :
      ( ~ r2_hidden(C_136,B_137)
      | k1_xboole_0 != B_137 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2335,c_2444])).

tff(c_2507,plain,(
    ! [A_138,B_139] :
      ( k3_xboole_0(A_138,B_139) != k1_xboole_0
      | r1_xboole_0(A_138,B_139) ) ),
    inference(resolution,[status(thm)],[c_4,c_2502])).

tff(c_2138,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_2516,plain,(
    k3_xboole_0(k1_relat_1('#skF_3'),'#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2507,c_2138])).

tff(c_2521,plain,(
    k3_xboole_0('#skF_2',k1_relat_1('#skF_3')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2516])).

tff(c_3112,plain,
    ( k1_relat_1(k7_relat_1('#skF_3','#skF_2')) != k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3088,c_2521])).

tff(c_3168,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2137,c_3112])).

tff(c_2142,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2137,c_22])).

tff(c_2146,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2142])).

tff(c_2191,plain,(
    ! [B_113,A_114] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_113,A_114)),A_114)
      | ~ v1_relat_1(B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_12,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ r1_tarski(A_10,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2199,plain,(
    ! [B_113] :
      ( k1_relat_1(k7_relat_1(B_113,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_113) ) ),
    inference(resolution,[status(thm)],[c_2191,c_12])).

tff(c_2167,plain,(
    ! [A_110] :
      ( k1_relat_1(A_110) != k1_xboole_0
      | k1_xboole_0 = A_110
      | ~ v1_relat_1(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_5176,plain,(
    ! [A_201,B_202] :
      ( k1_relat_1(k7_relat_1(A_201,B_202)) != k1_xboole_0
      | k7_relat_1(A_201,B_202) = k1_xboole_0
      | ~ v1_relat_1(A_201) ) ),
    inference(resolution,[status(thm)],[c_22,c_2167])).

tff(c_5186,plain,(
    ! [B_203] :
      ( k7_relat_1(B_203,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_203) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2199,c_5176])).

tff(c_5196,plain,(
    k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2146,c_5186])).

tff(c_5205,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5196,c_2199])).

tff(c_5217,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2146,c_5205])).

tff(c_5219,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3168,c_5217])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:12:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.57/2.01  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.57/2.02  
% 4.57/2.02  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.57/2.02  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.57/2.02  
% 4.57/2.02  %Foreground sorts:
% 4.57/2.02  
% 4.57/2.02  
% 4.57/2.02  %Background operators:
% 4.57/2.02  
% 4.57/2.02  
% 4.57/2.02  %Foreground operators:
% 4.57/2.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.57/2.02  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.57/2.02  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.57/2.02  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.57/2.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.57/2.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.57/2.02  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.57/2.02  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.57/2.02  tff('#skF_2', type, '#skF_2': $i).
% 4.57/2.02  tff('#skF_3', type, '#skF_3': $i).
% 4.57/2.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.57/2.02  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.57/2.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.57/2.02  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.57/2.02  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.57/2.02  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.57/2.02  
% 4.57/2.04  tff(f_84, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 4.57/2.04  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.57/2.04  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 4.57/2.04  tff(f_43, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 4.57/2.04  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.57/2.04  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.57/2.04  tff(f_57, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.57/2.04  tff(f_61, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 4.57/2.04  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 4.57/2.04  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.57/2.04  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 4.57/2.04  tff(f_49, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 4.57/2.04  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.57/2.04  tff(c_40, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.57/2.04  tff(c_141, plain, (r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_40])).
% 4.57/2.04  tff(c_34, plain, (~r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2') | k7_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.57/2.04  tff(c_169, plain, (k7_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_141, c_34])).
% 4.57/2.04  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.57/2.04  tff(c_577, plain, (![B_65, A_66]: (k3_xboole_0(k1_relat_1(B_65), A_66)=k1_relat_1(k7_relat_1(B_65, A_66)) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.57/2.04  tff(c_1960, plain, (![B_105, B_106]: (k3_xboole_0(B_105, k1_relat_1(B_106))=k1_relat_1(k7_relat_1(B_106, B_105)) | ~v1_relat_1(B_106))), inference(superposition, [status(thm), theory('equality')], [c_2, c_577])).
% 4.57/2.04  tff(c_8, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.57/2.04  tff(c_10, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.57/2.04  tff(c_194, plain, (![A_42, B_43]: (k4_xboole_0(A_42, k4_xboole_0(A_42, B_43))=k3_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.57/2.04  tff(c_212, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k3_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_194])).
% 4.57/2.04  tff(c_216, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_212])).
% 4.57/2.04  tff(c_163, plain, (![A_34, B_35]: (k4_xboole_0(A_34, B_35)=A_34 | ~r1_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.57/2.04  tff(c_167, plain, (k4_xboole_0(k1_relat_1('#skF_3'), '#skF_2')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_141, c_163])).
% 4.57/2.04  tff(c_209, plain, (k4_xboole_0(k1_relat_1('#skF_3'), k1_relat_1('#skF_3'))=k3_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_167, c_194])).
% 4.57/2.04  tff(c_215, plain, (k4_xboole_0(k1_relat_1('#skF_3'), k1_relat_1('#skF_3'))=k3_xboole_0('#skF_2', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_209])).
% 4.57/2.04  tff(c_270, plain, (k3_xboole_0('#skF_2', k1_relat_1('#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_216, c_215])).
% 4.57/2.04  tff(c_2025, plain, (k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1960, c_270])).
% 4.57/2.04  tff(c_2093, plain, (k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2025])).
% 4.57/2.04  tff(c_22, plain, (![A_17, B_18]: (v1_relat_1(k7_relat_1(A_17, B_18)) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.57/2.04  tff(c_628, plain, (![B_2, B_65]: (k3_xboole_0(B_2, k1_relat_1(B_65))=k1_relat_1(k7_relat_1(B_65, B_2)) | ~v1_relat_1(B_65))), inference(superposition, [status(thm), theory('equality')], [c_2, c_577])).
% 4.57/2.04  tff(c_2101, plain, (![B_2]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_3', '#skF_2'), B_2))=k3_xboole_0(B_2, k1_xboole_0) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_2093, c_628])).
% 4.57/2.04  tff(c_2110, plain, (![B_2]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_3', '#skF_2'), B_2))=k1_xboole_0 | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2101])).
% 4.57/2.04  tff(c_2116, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_2110])).
% 4.57/2.04  tff(c_2119, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_2116])).
% 4.57/2.04  tff(c_2123, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_2119])).
% 4.57/2.04  tff(c_2125, plain, (v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_2110])).
% 4.57/2.04  tff(c_26, plain, (![A_19]: (k1_relat_1(A_19)!=k1_xboole_0 | k1_xboole_0=A_19 | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.57/2.04  tff(c_2128, plain, (k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))!=k1_xboole_0 | k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_2125, c_26])).
% 4.57/2.04  tff(c_2134, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2093, c_2128])).
% 4.57/2.04  tff(c_2136, plain, $false, inference(negUnitSimplification, [status(thm)], [c_169, c_2134])).
% 4.57/2.04  tff(c_2137, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 4.57/2.04  tff(c_2449, plain, (![B_134, A_135]: (k3_xboole_0(k1_relat_1(B_134), A_135)=k1_relat_1(k7_relat_1(B_134, A_135)) | ~v1_relat_1(B_134))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.57/2.04  tff(c_3088, plain, (![A_163, B_164]: (k3_xboole_0(A_163, k1_relat_1(B_164))=k1_relat_1(k7_relat_1(B_164, A_163)) | ~v1_relat_1(B_164))), inference(superposition, [status(thm), theory('equality')], [c_2449, c_2])).
% 4.57/2.04  tff(c_4, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), k3_xboole_0(A_3, B_4)) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.57/2.04  tff(c_2297, plain, (![A_124, B_125]: (k4_xboole_0(A_124, k4_xboole_0(A_124, B_125))=k3_xboole_0(A_124, B_125))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.57/2.04  tff(c_2326, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k3_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_2297])).
% 4.57/2.04  tff(c_2335, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2326])).
% 4.57/2.04  tff(c_20, plain, (![A_15, B_16]: (r1_xboole_0(A_15, B_16) | k4_xboole_0(A_15, B_16)!=A_15)), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.57/2.04  tff(c_2367, plain, (![A_130]: (k4_xboole_0(A_130, A_130)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2326])).
% 4.57/2.04  tff(c_16, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.57/2.04  tff(c_2372, plain, (![A_130]: (k4_xboole_0(A_130, k1_xboole_0)=k3_xboole_0(A_130, A_130))), inference(superposition, [status(thm), theory('equality')], [c_2367, c_16])).
% 4.57/2.04  tff(c_2396, plain, (![A_131]: (k3_xboole_0(A_131, A_131)=A_131)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_2372])).
% 4.57/2.04  tff(c_6, plain, (![A_3, B_4, C_7]: (~r1_xboole_0(A_3, B_4) | ~r2_hidden(C_7, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.57/2.04  tff(c_2435, plain, (![A_132, C_133]: (~r1_xboole_0(A_132, A_132) | ~r2_hidden(C_133, A_132))), inference(superposition, [status(thm), theory('equality')], [c_2396, c_6])).
% 4.57/2.04  tff(c_2444, plain, (![C_133, B_16]: (~r2_hidden(C_133, B_16) | k4_xboole_0(B_16, B_16)!=B_16)), inference(resolution, [status(thm)], [c_20, c_2435])).
% 4.57/2.04  tff(c_2502, plain, (![C_136, B_137]: (~r2_hidden(C_136, B_137) | k1_xboole_0!=B_137)), inference(demodulation, [status(thm), theory('equality')], [c_2335, c_2444])).
% 4.57/2.04  tff(c_2507, plain, (![A_138, B_139]: (k3_xboole_0(A_138, B_139)!=k1_xboole_0 | r1_xboole_0(A_138, B_139))), inference(resolution, [status(thm)], [c_4, c_2502])).
% 4.57/2.04  tff(c_2138, plain, (~r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_40])).
% 4.57/2.04  tff(c_2516, plain, (k3_xboole_0(k1_relat_1('#skF_3'), '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_2507, c_2138])).
% 4.57/2.04  tff(c_2521, plain, (k3_xboole_0('#skF_2', k1_relat_1('#skF_3'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2516])).
% 4.57/2.04  tff(c_3112, plain, (k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))!=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3088, c_2521])).
% 4.57/2.04  tff(c_3168, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2137, c_3112])).
% 4.57/2.04  tff(c_2142, plain, (v1_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2137, c_22])).
% 4.57/2.04  tff(c_2146, plain, (v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2142])).
% 4.57/2.04  tff(c_2191, plain, (![B_113, A_114]: (r1_tarski(k1_relat_1(k7_relat_1(B_113, A_114)), A_114) | ~v1_relat_1(B_113))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.57/2.04  tff(c_12, plain, (![A_10]: (k1_xboole_0=A_10 | ~r1_tarski(A_10, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.57/2.04  tff(c_2199, plain, (![B_113]: (k1_relat_1(k7_relat_1(B_113, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_113))), inference(resolution, [status(thm)], [c_2191, c_12])).
% 4.57/2.04  tff(c_2167, plain, (![A_110]: (k1_relat_1(A_110)!=k1_xboole_0 | k1_xboole_0=A_110 | ~v1_relat_1(A_110))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.57/2.04  tff(c_5176, plain, (![A_201, B_202]: (k1_relat_1(k7_relat_1(A_201, B_202))!=k1_xboole_0 | k7_relat_1(A_201, B_202)=k1_xboole_0 | ~v1_relat_1(A_201))), inference(resolution, [status(thm)], [c_22, c_2167])).
% 4.57/2.04  tff(c_5186, plain, (![B_203]: (k7_relat_1(B_203, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_203))), inference(superposition, [status(thm), theory('equality')], [c_2199, c_5176])).
% 4.57/2.04  tff(c_5196, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2146, c_5186])).
% 4.57/2.04  tff(c_5205, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5196, c_2199])).
% 4.57/2.04  tff(c_5217, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2146, c_5205])).
% 4.57/2.04  tff(c_5219, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3168, c_5217])).
% 4.57/2.04  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.57/2.04  
% 4.57/2.04  Inference rules
% 4.57/2.04  ----------------------
% 4.57/2.04  #Ref     : 0
% 4.57/2.04  #Sup     : 1275
% 4.57/2.04  #Fact    : 0
% 4.57/2.04  #Define  : 0
% 4.57/2.04  #Split   : 11
% 4.57/2.04  #Chain   : 0
% 4.57/2.04  #Close   : 0
% 4.57/2.04  
% 4.57/2.04  Ordering : KBO
% 4.57/2.04  
% 4.57/2.04  Simplification rules
% 4.57/2.04  ----------------------
% 4.57/2.04  #Subsume      : 143
% 4.57/2.04  #Demod        : 1178
% 4.57/2.04  #Tautology    : 769
% 4.57/2.04  #SimpNegUnit  : 9
% 4.57/2.04  #BackRed      : 0
% 4.57/2.04  
% 4.57/2.04  #Partial instantiations: 0
% 4.57/2.04  #Strategies tried      : 1
% 4.57/2.04  
% 4.57/2.04  Timing (in seconds)
% 4.57/2.04  ----------------------
% 4.57/2.04  Preprocessing        : 0.33
% 4.57/2.04  Parsing              : 0.18
% 4.57/2.04  CNF conversion       : 0.02
% 4.57/2.04  Main loop            : 0.81
% 4.57/2.04  Inferencing          : 0.26
% 4.57/2.04  Reduction            : 0.36
% 4.57/2.04  Demodulation         : 0.29
% 4.57/2.04  BG Simplification    : 0.03
% 4.57/2.04  Subsumption          : 0.11
% 4.57/2.04  Abstraction          : 0.04
% 4.57/2.04  MUC search           : 0.00
% 4.57/2.04  Cooper               : 0.00
% 4.57/2.04  Total                : 1.18
% 4.57/2.04  Index Insertion      : 0.00
% 4.57/2.04  Index Deletion       : 0.00
% 4.57/2.04  Index Matching       : 0.00
% 4.57/2.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
