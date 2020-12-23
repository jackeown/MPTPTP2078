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
% DateTime   : Thu Dec  3 09:53:44 EST 2020

% Result     : Theorem 4.53s
% Output     : CNFRefutation 4.78s
% Verified   : 
% Statistics : Number of formulae       :  192 ( 886 expanded)
%              Number of leaves         :   32 ( 282 expanded)
%              Depth                    :   10
%              Number of atoms          :  240 (1516 expanded)
%              Number of equality atoms :  104 ( 970 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_1 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_51,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_55,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k1_xboole_0
      <=> ( A = k1_xboole_0
          | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_77,plain,(
    ! [A_56,B_57] : r1_xboole_0(k4_xboole_0(A_56,B_57),B_57) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_80,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_77])).

tff(c_8,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1873,plain,(
    ! [A_222,B_223,C_224] :
      ( ~ r1_xboole_0(A_222,B_223)
      | ~ r2_hidden(C_224,k3_xboole_0(A_222,B_223)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1880,plain,(
    ! [A_8,C_224] :
      ( ~ r1_xboole_0(A_8,k1_xboole_0)
      | ~ r2_hidden(C_224,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1873])).

tff(c_1883,plain,(
    ! [C_224] : ~ r2_hidden(C_224,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1880])).

tff(c_50,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_83,plain,(
    k1_xboole_0 != '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_54,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_82,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_106,plain,(
    ! [A_64,B_65,C_66] :
      ( ~ r1_xboole_0(A_64,B_65)
      | ~ r2_hidden(C_66,k3_xboole_0(A_64,B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_113,plain,(
    ! [A_8,C_66] :
      ( ~ r1_xboole_0(A_8,k1_xboole_0)
      | ~ r2_hidden(C_66,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_106])).

tff(c_116,plain,(
    ! [C_66] : ~ r2_hidden(C_66,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_113])).

tff(c_60,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_101,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_579,plain,(
    ! [A_103,B_104,C_105,D_106] :
      ( r2_hidden(k4_tarski(A_103,B_104),k2_zfmisc_1(C_105,D_106))
      | ~ r2_hidden(B_104,D_106)
      | ~ r2_hidden(A_103,C_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_591,plain,(
    ! [A_103,B_104] :
      ( r2_hidden(k4_tarski(A_103,B_104),k1_xboole_0)
      | ~ r2_hidden(B_104,'#skF_12')
      | ~ r2_hidden(A_103,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_579])).

tff(c_595,plain,(
    ! [B_104,A_103] :
      ( ~ r2_hidden(B_104,'#skF_12')
      | ~ r2_hidden(A_103,'#skF_11') ) ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_591])).

tff(c_597,plain,(
    ! [A_107] : ~ r2_hidden(A_107,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_595])).

tff(c_601,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_6,c_597])).

tff(c_605,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_601])).

tff(c_607,plain,(
    ! [B_108] : ~ r2_hidden(B_108,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_595])).

tff(c_611,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(resolution,[status(thm)],[c_6,c_607])).

tff(c_615,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_611])).

tff(c_616,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_618,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_616])).

tff(c_620,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_618,c_6])).

tff(c_1232,plain,(
    ! [A_164,B_165,D_166] :
      ( r2_hidden('#skF_8'(A_164,B_165,k2_zfmisc_1(A_164,B_165),D_166),B_165)
      | ~ r2_hidden(D_166,k2_zfmisc_1(A_164,B_165)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_623,plain,(
    ! [A_9] : r1_xboole_0(A_9,'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_618,c_80])).

tff(c_624,plain,(
    ! [A_8] : k3_xboole_0(A_8,'#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_618,c_618,c_8])).

tff(c_658,plain,(
    ! [A_113,B_114,C_115] :
      ( ~ r1_xboole_0(A_113,B_114)
      | ~ r2_hidden(C_115,k3_xboole_0(A_113,B_114)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_665,plain,(
    ! [A_8,C_115] :
      ( ~ r1_xboole_0(A_8,'#skF_10')
      | ~ r2_hidden(C_115,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_624,c_658])).

tff(c_668,plain,(
    ! [C_115] : ~ r2_hidden(C_115,'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_623,c_665])).

tff(c_1251,plain,(
    ! [D_167,A_168] : ~ r2_hidden(D_167,k2_zfmisc_1(A_168,'#skF_10')) ),
    inference(resolution,[status(thm)],[c_1232,c_668])).

tff(c_1279,plain,(
    ! [A_168] : k2_zfmisc_1(A_168,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_620,c_1251])).

tff(c_58,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_100,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_619,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_618,c_100])).

tff(c_1283,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1279,c_619])).

tff(c_1284,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_616])).

tff(c_1289,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1284,c_6])).

tff(c_1823,plain,(
    ! [A_217,B_218,D_219] :
      ( r2_hidden('#skF_7'(A_217,B_218,k2_zfmisc_1(A_217,B_218),D_219),A_217)
      | ~ r2_hidden(D_219,k2_zfmisc_1(A_217,B_218)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1292,plain,(
    ! [A_9] : r1_xboole_0(A_9,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1284,c_80])).

tff(c_1293,plain,(
    ! [A_8] : k3_xboole_0(A_8,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1284,c_1284,c_8])).

tff(c_1324,plain,(
    ! [A_172,B_173,C_174] :
      ( ~ r1_xboole_0(A_172,B_173)
      | ~ r2_hidden(C_174,k3_xboole_0(A_172,B_173)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1327,plain,(
    ! [A_8,C_174] :
      ( ~ r1_xboole_0(A_8,'#skF_9')
      | ~ r2_hidden(C_174,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1293,c_1324])).

tff(c_1329,plain,(
    ! [C_174] : ~ r2_hidden(C_174,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1292,c_1327])).

tff(c_1838,plain,(
    ! [D_220,B_221] : ~ r2_hidden(D_220,k2_zfmisc_1('#skF_9',B_221)) ),
    inference(resolution,[status(thm)],[c_1823,c_1329])).

tff(c_1858,plain,(
    ! [B_221] : k2_zfmisc_1('#skF_9',B_221) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1289,c_1838])).

tff(c_1288,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1284,c_100])).

tff(c_1862,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1858,c_1288])).

tff(c_1864,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_2370,plain,(
    ! [A_262,B_263,C_264,D_265] :
      ( r2_hidden(k4_tarski(A_262,B_263),k2_zfmisc_1(C_264,D_265))
      | ~ r2_hidden(B_263,D_265)
      | ~ r2_hidden(A_262,C_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2382,plain,(
    ! [A_262,B_263] :
      ( r2_hidden(k4_tarski(A_262,B_263),k1_xboole_0)
      | ~ r2_hidden(B_263,'#skF_10')
      | ~ r2_hidden(A_262,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1864,c_2370])).

tff(c_2389,plain,(
    ! [B_263,A_262] :
      ( ~ r2_hidden(B_263,'#skF_10')
      | ~ r2_hidden(A_262,'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1883,c_2382])).

tff(c_2407,plain,(
    ! [A_267] : ~ r2_hidden(A_267,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_2389])).

tff(c_2417,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_6,c_2407])).

tff(c_2433,plain,(
    '#skF_9' != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2417,c_83])).

tff(c_1884,plain,(
    ! [A_225,B_226] : k4_xboole_0(A_225,k4_xboole_0(A_225,B_226)) = k3_xboole_0(A_225,B_226) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1902,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k3_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1884])).

tff(c_1913,plain,(
    ! [A_228] : k4_xboole_0(A_228,A_228) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1902])).

tff(c_12,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1918,plain,(
    ! [A_228] : k4_xboole_0(A_228,k1_xboole_0) = k3_xboole_0(A_228,A_228) ),
    inference(superposition,[status(thm),theory(equality)],[c_1913,c_12])).

tff(c_1933,plain,(
    ! [A_228] : k3_xboole_0(A_228,A_228) = A_228 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1918])).

tff(c_2307,plain,(
    ! [A_257,B_258] :
      ( r2_hidden('#skF_1'(A_257,B_258),k3_xboole_0(A_257,B_258))
      | r1_xboole_0(A_257,B_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2325,plain,(
    ! [A_228] :
      ( r2_hidden('#skF_1'(A_228,A_228),A_228)
      | r1_xboole_0(A_228,A_228) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1933,c_2307])).

tff(c_2434,plain,(
    '#skF_11' != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2417,c_82])).

tff(c_1905,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1902])).

tff(c_2428,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2417,c_1905])).

tff(c_1863,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_2385,plain,(
    ! [A_262,B_263] :
      ( r2_hidden(k4_tarski(A_262,B_263),k1_xboole_0)
      | ~ r2_hidden(B_263,'#skF_12')
      | ~ r2_hidden(A_262,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1863,c_2370])).

tff(c_2390,plain,(
    ! [B_263,A_262] :
      ( ~ r2_hidden(B_263,'#skF_12')
      | ~ r2_hidden(A_262,'#skF_11') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1883,c_2385])).

tff(c_2680,plain,(
    ! [A_280] : ~ r2_hidden(A_280,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_2390])).

tff(c_2695,plain,(
    r1_xboole_0('#skF_11','#skF_11') ),
    inference(resolution,[status(thm)],[c_2325,c_2680])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,B_15) = A_14
      | ~ r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2700,plain,(
    k4_xboole_0('#skF_11','#skF_11') = '#skF_11' ),
    inference(resolution,[status(thm)],[c_2695,c_16])).

tff(c_2703,plain,(
    '#skF_11' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2428,c_2700])).

tff(c_2705,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2434,c_2703])).

tff(c_2707,plain,(
    ! [B_281] : ~ r2_hidden(B_281,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_2390])).

tff(c_2722,plain,(
    r1_xboole_0('#skF_12','#skF_12') ),
    inference(resolution,[status(thm)],[c_2325,c_2707])).

tff(c_2729,plain,(
    k4_xboole_0('#skF_12','#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_2722,c_16])).

tff(c_2792,plain,(
    '#skF_9' = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_2729,c_2428])).

tff(c_2810,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2433,c_2792])).

tff(c_2812,plain,(
    ! [B_286] : ~ r2_hidden(B_286,'#skF_10') ),
    inference(splitRight,[status(thm)],[c_2389])).

tff(c_2822,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_6,c_2812])).

tff(c_2838,plain,(
    '#skF_10' != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2822,c_83])).

tff(c_2839,plain,(
    '#skF_11' != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2822,c_82])).

tff(c_2833,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2822,c_1905])).

tff(c_3084,plain,(
    ! [A_299] : ~ r2_hidden(A_299,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_2390])).

tff(c_3099,plain,(
    r1_xboole_0('#skF_11','#skF_11') ),
    inference(resolution,[status(thm)],[c_2325,c_3084])).

tff(c_3104,plain,(
    k4_xboole_0('#skF_11','#skF_11') = '#skF_11' ),
    inference(resolution,[status(thm)],[c_3099,c_16])).

tff(c_3107,plain,(
    '#skF_11' = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2833,c_3104])).

tff(c_3109,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2839,c_3107])).

tff(c_3111,plain,(
    ! [B_300] : ~ r2_hidden(B_300,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_2390])).

tff(c_3126,plain,(
    r1_xboole_0('#skF_12','#skF_12') ),
    inference(resolution,[status(thm)],[c_2325,c_3111])).

tff(c_3133,plain,(
    k4_xboole_0('#skF_12','#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_3126,c_16])).

tff(c_3206,plain,(
    '#skF_10' = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_3133,c_2833])).

tff(c_3224,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2838,c_3206])).

tff(c_3226,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_3939,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3226,c_6])).

tff(c_4496,plain,(
    ! [A_420,B_421,D_422] :
      ( r2_hidden('#skF_8'(A_420,B_421,k2_zfmisc_1(A_420,B_421),D_422),B_421)
      | ~ r2_hidden(D_422,k2_zfmisc_1(A_420,B_421)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_3228,plain,(
    ! [A_9] : r1_xboole_0(A_9,'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3226,c_80])).

tff(c_3229,plain,(
    ! [A_8] : k3_xboole_0(A_8,'#skF_12') = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3226,c_3226,c_8])).

tff(c_3956,plain,(
    ! [A_371,B_372,C_373] :
      ( ~ r1_xboole_0(A_371,B_372)
      | ~ r2_hidden(C_373,k3_xboole_0(A_371,B_372)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3963,plain,(
    ! [A_8,C_373] :
      ( ~ r1_xboole_0(A_8,'#skF_12')
      | ~ r2_hidden(C_373,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3229,c_3956])).

tff(c_3966,plain,(
    ! [C_373] : ~ r2_hidden(C_373,'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3228,c_3963])).

tff(c_4515,plain,(
    ! [D_423,A_424] : ~ r2_hidden(D_423,k2_zfmisc_1(A_424,'#skF_12')) ),
    inference(resolution,[status(thm)],[c_4496,c_3966])).

tff(c_4538,plain,(
    ! [A_424] : k2_zfmisc_1(A_424,'#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_3939,c_4515])).

tff(c_3265,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3226,c_6])).

tff(c_3884,plain,(
    ! [A_360,B_361,D_362] :
      ( r2_hidden('#skF_7'(A_360,B_361,k2_zfmisc_1(A_360,B_361),D_362),A_360)
      | ~ r2_hidden(D_362,k2_zfmisc_1(A_360,B_361)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_3283,plain,(
    ! [A_313,B_314,C_315] :
      ( ~ r1_xboole_0(A_313,B_314)
      | ~ r2_hidden(C_315,k3_xboole_0(A_313,B_314)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3290,plain,(
    ! [A_8,C_315] :
      ( ~ r1_xboole_0(A_8,'#skF_12')
      | ~ r2_hidden(C_315,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3229,c_3283])).

tff(c_3293,plain,(
    ! [C_315] : ~ r2_hidden(C_315,'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3228,c_3290])).

tff(c_3899,plain,(
    ! [D_363,B_364] : ~ r2_hidden(D_363,k2_zfmisc_1('#skF_12',B_364)) ),
    inference(resolution,[status(thm)],[c_3884,c_3293])).

tff(c_3919,plain,(
    ! [B_364] : k2_zfmisc_1('#skF_12',B_364) = '#skF_12' ),
    inference(resolution,[status(thm)],[c_3265,c_3899])).

tff(c_52,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3251,plain,
    ( '#skF_10' = '#skF_12'
    | '#skF_9' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3226,c_3226,c_3226,c_52])).

tff(c_3252,plain,(
    '#skF_9' = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_3251])).

tff(c_3225,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_3249,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3226,c_3225])).

tff(c_3253,plain,(
    k2_zfmisc_1('#skF_12','#skF_10') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3252,c_3249])).

tff(c_3923,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3919,c_3253])).

tff(c_3924,plain,(
    '#skF_10' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_3251])).

tff(c_3926,plain,(
    k2_zfmisc_1('#skF_9','#skF_12') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3924,c_3249])).

tff(c_4542,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4538,c_3926])).

tff(c_4544,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_56,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4578,plain,
    ( '#skF_11' = '#skF_10'
    | '#skF_11' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4544,c_4544,c_4544,c_56])).

tff(c_4579,plain,(
    '#skF_11' = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_4578])).

tff(c_4585,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4579,c_4544])).

tff(c_4615,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4585,c_6])).

tff(c_5429,plain,(
    ! [A_491,B_492,D_493] :
      ( r2_hidden('#skF_7'(A_491,B_492,k2_zfmisc_1(A_491,B_492),D_493),A_491)
      | ~ r2_hidden(D_493,k2_zfmisc_1(A_491,B_492)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4545,plain,(
    ! [A_9] : r1_xboole_0(A_9,'#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4544,c_80])).

tff(c_4584,plain,(
    ! [A_9] : r1_xboole_0(A_9,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4579,c_4545])).

tff(c_4546,plain,(
    ! [A_8] : k3_xboole_0(A_8,'#skF_11') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4544,c_4544,c_8])).

tff(c_4582,plain,(
    ! [A_8] : k3_xboole_0(A_8,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4579,c_4579,c_4546])).

tff(c_4770,plain,(
    ! [A_443,B_444,C_445] :
      ( ~ r1_xboole_0(A_443,B_444)
      | ~ r2_hidden(C_445,k3_xboole_0(A_443,B_444)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4783,plain,(
    ! [A_8,C_445] :
      ( ~ r1_xboole_0(A_8,'#skF_9')
      | ~ r2_hidden(C_445,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4582,c_4770])).

tff(c_4788,plain,(
    ! [C_445] : ~ r2_hidden(C_445,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4584,c_4783])).

tff(c_5444,plain,(
    ! [D_494,B_495] : ~ r2_hidden(D_494,k2_zfmisc_1('#skF_9',B_495)) ),
    inference(resolution,[status(thm)],[c_5429,c_4788])).

tff(c_5464,plain,(
    ! [B_495] : k2_zfmisc_1('#skF_9',B_495) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_4615,c_5444])).

tff(c_4543,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_4553,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4544,c_4543])).

tff(c_4583,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4579,c_4553])).

tff(c_5468,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5464,c_4583])).

tff(c_5469,plain,(
    '#skF_11' = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_4578])).

tff(c_5475,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5469,c_4544])).

tff(c_5510,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5475,c_6])).

tff(c_6128,plain,(
    ! [A_558,B_559,D_560] :
      ( r2_hidden('#skF_8'(A_558,B_559,k2_zfmisc_1(A_558,B_559),D_560),B_559)
      | ~ r2_hidden(D_560,k2_zfmisc_1(A_558,B_559)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_5474,plain,(
    ! [A_9] : r1_xboole_0(A_9,'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5469,c_4545])).

tff(c_5472,plain,(
    ! [A_8] : k3_xboole_0(A_8,'#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5469,c_5469,c_4546])).

tff(c_5529,plain,(
    ! [A_504,B_505,C_506] :
      ( ~ r1_xboole_0(A_504,B_505)
      | ~ r2_hidden(C_506,k3_xboole_0(A_504,B_505)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5536,plain,(
    ! [A_8,C_506] :
      ( ~ r1_xboole_0(A_8,'#skF_10')
      | ~ r2_hidden(C_506,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5472,c_5529])).

tff(c_5539,plain,(
    ! [C_506] : ~ r2_hidden(C_506,'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5474,c_5536])).

tff(c_6152,plain,(
    ! [D_561,A_562] : ~ r2_hidden(D_561,k2_zfmisc_1(A_562,'#skF_10')) ),
    inference(resolution,[status(thm)],[c_6128,c_5539])).

tff(c_6180,plain,(
    ! [A_562] : k2_zfmisc_1(A_562,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_5510,c_6152])).

tff(c_5473,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5469,c_4553])).

tff(c_6184,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6180,c_5473])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:54:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.53/1.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.72/1.94  
% 4.72/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.78/1.95  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_1 > #skF_12
% 4.78/1.95  
% 4.78/1.95  %Foreground sorts:
% 4.78/1.95  
% 4.78/1.95  
% 4.78/1.95  %Background operators:
% 4.78/1.95  
% 4.78/1.95  
% 4.78/1.95  %Foreground operators:
% 4.78/1.95  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.78/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.78/1.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.78/1.95  tff('#skF_11', type, '#skF_11': $i).
% 4.78/1.95  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 4.78/1.95  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.78/1.95  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.78/1.95  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.78/1.95  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.78/1.95  tff('#skF_10', type, '#skF_10': $i).
% 4.78/1.95  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 4.78/1.95  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 4.78/1.95  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.78/1.95  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 4.78/1.95  tff('#skF_9', type, '#skF_9': $i).
% 4.78/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.78/1.95  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.78/1.95  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.78/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.78/1.95  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.78/1.95  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.78/1.95  tff('#skF_12', type, '#skF_12': $i).
% 4.78/1.95  
% 4.78/1.97  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.78/1.97  tff(f_51, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.78/1.97  tff(f_55, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 4.78/1.97  tff(f_49, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 4.78/1.97  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.78/1.97  tff(f_84, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.78/1.97  tff(f_77, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 4.78/1.97  tff(f_71, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 4.78/1.97  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.78/1.97  tff(f_59, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.78/1.97  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.78/1.97  tff(c_10, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.78/1.97  tff(c_77, plain, (![A_56, B_57]: (r1_xboole_0(k4_xboole_0(A_56, B_57), B_57))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.78/1.97  tff(c_80, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_77])).
% 4.78/1.97  tff(c_8, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.78/1.97  tff(c_1873, plain, (![A_222, B_223, C_224]: (~r1_xboole_0(A_222, B_223) | ~r2_hidden(C_224, k3_xboole_0(A_222, B_223)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.78/1.97  tff(c_1880, plain, (![A_8, C_224]: (~r1_xboole_0(A_8, k1_xboole_0) | ~r2_hidden(C_224, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1873])).
% 4.78/1.97  tff(c_1883, plain, (![C_224]: (~r2_hidden(C_224, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1880])).
% 4.78/1.97  tff(c_50, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.78/1.97  tff(c_83, plain, (k1_xboole_0!='#skF_12'), inference(splitLeft, [status(thm)], [c_50])).
% 4.78/1.97  tff(c_54, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.78/1.97  tff(c_82, plain, (k1_xboole_0!='#skF_11'), inference(splitLeft, [status(thm)], [c_54])).
% 4.78/1.97  tff(c_106, plain, (![A_64, B_65, C_66]: (~r1_xboole_0(A_64, B_65) | ~r2_hidden(C_66, k3_xboole_0(A_64, B_65)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.78/1.97  tff(c_113, plain, (![A_8, C_66]: (~r1_xboole_0(A_8, k1_xboole_0) | ~r2_hidden(C_66, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_106])).
% 4.78/1.97  tff(c_116, plain, (![C_66]: (~r2_hidden(C_66, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_113])).
% 4.78/1.97  tff(c_60, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.78/1.97  tff(c_101, plain, (k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_60])).
% 4.78/1.97  tff(c_579, plain, (![A_103, B_104, C_105, D_106]: (r2_hidden(k4_tarski(A_103, B_104), k2_zfmisc_1(C_105, D_106)) | ~r2_hidden(B_104, D_106) | ~r2_hidden(A_103, C_105))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.78/1.97  tff(c_591, plain, (![A_103, B_104]: (r2_hidden(k4_tarski(A_103, B_104), k1_xboole_0) | ~r2_hidden(B_104, '#skF_12') | ~r2_hidden(A_103, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_101, c_579])).
% 4.78/1.97  tff(c_595, plain, (![B_104, A_103]: (~r2_hidden(B_104, '#skF_12') | ~r2_hidden(A_103, '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_116, c_591])).
% 4.78/1.97  tff(c_597, plain, (![A_107]: (~r2_hidden(A_107, '#skF_11'))), inference(splitLeft, [status(thm)], [c_595])).
% 4.78/1.97  tff(c_601, plain, (k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_6, c_597])).
% 4.78/1.97  tff(c_605, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_601])).
% 4.78/1.97  tff(c_607, plain, (![B_108]: (~r2_hidden(B_108, '#skF_12'))), inference(splitRight, [status(thm)], [c_595])).
% 4.78/1.97  tff(c_611, plain, (k1_xboole_0='#skF_12'), inference(resolution, [status(thm)], [c_6, c_607])).
% 4.78/1.97  tff(c_615, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_611])).
% 4.78/1.97  tff(c_616, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_60])).
% 4.78/1.97  tff(c_618, plain, (k1_xboole_0='#skF_10'), inference(splitLeft, [status(thm)], [c_616])).
% 4.78/1.97  tff(c_620, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_618, c_6])).
% 4.78/1.97  tff(c_1232, plain, (![A_164, B_165, D_166]: (r2_hidden('#skF_8'(A_164, B_165, k2_zfmisc_1(A_164, B_165), D_166), B_165) | ~r2_hidden(D_166, k2_zfmisc_1(A_164, B_165)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.78/1.97  tff(c_623, plain, (![A_9]: (r1_xboole_0(A_9, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_618, c_80])).
% 4.78/1.97  tff(c_624, plain, (![A_8]: (k3_xboole_0(A_8, '#skF_10')='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_618, c_618, c_8])).
% 4.78/1.97  tff(c_658, plain, (![A_113, B_114, C_115]: (~r1_xboole_0(A_113, B_114) | ~r2_hidden(C_115, k3_xboole_0(A_113, B_114)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.78/1.97  tff(c_665, plain, (![A_8, C_115]: (~r1_xboole_0(A_8, '#skF_10') | ~r2_hidden(C_115, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_624, c_658])).
% 4.78/1.97  tff(c_668, plain, (![C_115]: (~r2_hidden(C_115, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_623, c_665])).
% 4.78/1.97  tff(c_1251, plain, (![D_167, A_168]: (~r2_hidden(D_167, k2_zfmisc_1(A_168, '#skF_10')))), inference(resolution, [status(thm)], [c_1232, c_668])).
% 4.78/1.97  tff(c_1279, plain, (![A_168]: (k2_zfmisc_1(A_168, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_620, c_1251])).
% 4.78/1.97  tff(c_58, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.78/1.97  tff(c_100, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_58])).
% 4.78/1.97  tff(c_619, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_618, c_100])).
% 4.78/1.97  tff(c_1283, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1279, c_619])).
% 4.78/1.97  tff(c_1284, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_616])).
% 4.78/1.97  tff(c_1289, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1284, c_6])).
% 4.78/1.97  tff(c_1823, plain, (![A_217, B_218, D_219]: (r2_hidden('#skF_7'(A_217, B_218, k2_zfmisc_1(A_217, B_218), D_219), A_217) | ~r2_hidden(D_219, k2_zfmisc_1(A_217, B_218)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.78/1.97  tff(c_1292, plain, (![A_9]: (r1_xboole_0(A_9, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_1284, c_80])).
% 4.78/1.97  tff(c_1293, plain, (![A_8]: (k3_xboole_0(A_8, '#skF_9')='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1284, c_1284, c_8])).
% 4.78/1.97  tff(c_1324, plain, (![A_172, B_173, C_174]: (~r1_xboole_0(A_172, B_173) | ~r2_hidden(C_174, k3_xboole_0(A_172, B_173)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.78/1.97  tff(c_1327, plain, (![A_8, C_174]: (~r1_xboole_0(A_8, '#skF_9') | ~r2_hidden(C_174, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1293, c_1324])).
% 4.78/1.97  tff(c_1329, plain, (![C_174]: (~r2_hidden(C_174, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_1292, c_1327])).
% 4.78/1.97  tff(c_1838, plain, (![D_220, B_221]: (~r2_hidden(D_220, k2_zfmisc_1('#skF_9', B_221)))), inference(resolution, [status(thm)], [c_1823, c_1329])).
% 4.78/1.97  tff(c_1858, plain, (![B_221]: (k2_zfmisc_1('#skF_9', B_221)='#skF_9')), inference(resolution, [status(thm)], [c_1289, c_1838])).
% 4.78/1.97  tff(c_1288, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1284, c_100])).
% 4.78/1.97  tff(c_1862, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1858, c_1288])).
% 4.78/1.97  tff(c_1864, plain, (k2_zfmisc_1('#skF_9', '#skF_10')=k1_xboole_0), inference(splitRight, [status(thm)], [c_58])).
% 4.78/1.97  tff(c_2370, plain, (![A_262, B_263, C_264, D_265]: (r2_hidden(k4_tarski(A_262, B_263), k2_zfmisc_1(C_264, D_265)) | ~r2_hidden(B_263, D_265) | ~r2_hidden(A_262, C_264))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.78/1.97  tff(c_2382, plain, (![A_262, B_263]: (r2_hidden(k4_tarski(A_262, B_263), k1_xboole_0) | ~r2_hidden(B_263, '#skF_10') | ~r2_hidden(A_262, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1864, c_2370])).
% 4.78/1.97  tff(c_2389, plain, (![B_263, A_262]: (~r2_hidden(B_263, '#skF_10') | ~r2_hidden(A_262, '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_1883, c_2382])).
% 4.78/1.97  tff(c_2407, plain, (![A_267]: (~r2_hidden(A_267, '#skF_9'))), inference(splitLeft, [status(thm)], [c_2389])).
% 4.78/1.97  tff(c_2417, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_6, c_2407])).
% 4.78/1.97  tff(c_2433, plain, ('#skF_9'!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_2417, c_83])).
% 4.78/1.97  tff(c_1884, plain, (![A_225, B_226]: (k4_xboole_0(A_225, k4_xboole_0(A_225, B_226))=k3_xboole_0(A_225, B_226))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.78/1.97  tff(c_1902, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k3_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1884])).
% 4.78/1.97  tff(c_1913, plain, (![A_228]: (k4_xboole_0(A_228, A_228)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1902])).
% 4.78/1.97  tff(c_12, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.78/1.97  tff(c_1918, plain, (![A_228]: (k4_xboole_0(A_228, k1_xboole_0)=k3_xboole_0(A_228, A_228))), inference(superposition, [status(thm), theory('equality')], [c_1913, c_12])).
% 4.78/1.97  tff(c_1933, plain, (![A_228]: (k3_xboole_0(A_228, A_228)=A_228)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1918])).
% 4.78/1.97  tff(c_2307, plain, (![A_257, B_258]: (r2_hidden('#skF_1'(A_257, B_258), k3_xboole_0(A_257, B_258)) | r1_xboole_0(A_257, B_258))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.78/1.97  tff(c_2325, plain, (![A_228]: (r2_hidden('#skF_1'(A_228, A_228), A_228) | r1_xboole_0(A_228, A_228))), inference(superposition, [status(thm), theory('equality')], [c_1933, c_2307])).
% 4.78/1.97  tff(c_2434, plain, ('#skF_11'!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_2417, c_82])).
% 4.78/1.97  tff(c_1905, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1902])).
% 4.78/1.97  tff(c_2428, plain, (![A_9]: (k4_xboole_0(A_9, A_9)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2417, c_1905])).
% 4.78/1.97  tff(c_1863, plain, (k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(splitRight, [status(thm)], [c_58])).
% 4.78/1.97  tff(c_2385, plain, (![A_262, B_263]: (r2_hidden(k4_tarski(A_262, B_263), k1_xboole_0) | ~r2_hidden(B_263, '#skF_12') | ~r2_hidden(A_262, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_1863, c_2370])).
% 4.78/1.97  tff(c_2390, plain, (![B_263, A_262]: (~r2_hidden(B_263, '#skF_12') | ~r2_hidden(A_262, '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_1883, c_2385])).
% 4.78/1.97  tff(c_2680, plain, (![A_280]: (~r2_hidden(A_280, '#skF_11'))), inference(splitLeft, [status(thm)], [c_2390])).
% 4.78/1.97  tff(c_2695, plain, (r1_xboole_0('#skF_11', '#skF_11')), inference(resolution, [status(thm)], [c_2325, c_2680])).
% 4.78/1.97  tff(c_16, plain, (![A_14, B_15]: (k4_xboole_0(A_14, B_15)=A_14 | ~r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.78/1.97  tff(c_2700, plain, (k4_xboole_0('#skF_11', '#skF_11')='#skF_11'), inference(resolution, [status(thm)], [c_2695, c_16])).
% 4.78/1.97  tff(c_2703, plain, ('#skF_11'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_2428, c_2700])).
% 4.78/1.97  tff(c_2705, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2434, c_2703])).
% 4.78/1.97  tff(c_2707, plain, (![B_281]: (~r2_hidden(B_281, '#skF_12'))), inference(splitRight, [status(thm)], [c_2390])).
% 4.78/1.97  tff(c_2722, plain, (r1_xboole_0('#skF_12', '#skF_12')), inference(resolution, [status(thm)], [c_2325, c_2707])).
% 4.78/1.97  tff(c_2729, plain, (k4_xboole_0('#skF_12', '#skF_12')='#skF_12'), inference(resolution, [status(thm)], [c_2722, c_16])).
% 4.78/1.97  tff(c_2792, plain, ('#skF_9'='#skF_12'), inference(superposition, [status(thm), theory('equality')], [c_2729, c_2428])).
% 4.78/1.97  tff(c_2810, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2433, c_2792])).
% 4.78/1.97  tff(c_2812, plain, (![B_286]: (~r2_hidden(B_286, '#skF_10'))), inference(splitRight, [status(thm)], [c_2389])).
% 4.78/1.97  tff(c_2822, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_6, c_2812])).
% 4.78/1.97  tff(c_2838, plain, ('#skF_10'!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_2822, c_83])).
% 4.78/1.97  tff(c_2839, plain, ('#skF_11'!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_2822, c_82])).
% 4.78/1.97  tff(c_2833, plain, (![A_9]: (k4_xboole_0(A_9, A_9)='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_2822, c_1905])).
% 4.78/1.97  tff(c_3084, plain, (![A_299]: (~r2_hidden(A_299, '#skF_11'))), inference(splitLeft, [status(thm)], [c_2390])).
% 4.78/1.97  tff(c_3099, plain, (r1_xboole_0('#skF_11', '#skF_11')), inference(resolution, [status(thm)], [c_2325, c_3084])).
% 4.78/1.97  tff(c_3104, plain, (k4_xboole_0('#skF_11', '#skF_11')='#skF_11'), inference(resolution, [status(thm)], [c_3099, c_16])).
% 4.78/1.97  tff(c_3107, plain, ('#skF_11'='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_2833, c_3104])).
% 4.78/1.97  tff(c_3109, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2839, c_3107])).
% 4.78/1.97  tff(c_3111, plain, (![B_300]: (~r2_hidden(B_300, '#skF_12'))), inference(splitRight, [status(thm)], [c_2390])).
% 4.78/1.97  tff(c_3126, plain, (r1_xboole_0('#skF_12', '#skF_12')), inference(resolution, [status(thm)], [c_2325, c_3111])).
% 4.78/1.97  tff(c_3133, plain, (k4_xboole_0('#skF_12', '#skF_12')='#skF_12'), inference(resolution, [status(thm)], [c_3126, c_16])).
% 4.78/1.97  tff(c_3206, plain, ('#skF_10'='#skF_12'), inference(superposition, [status(thm), theory('equality')], [c_3133, c_2833])).
% 4.78/1.97  tff(c_3224, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2838, c_3206])).
% 4.78/1.97  tff(c_3226, plain, (k1_xboole_0='#skF_12'), inference(splitRight, [status(thm)], [c_50])).
% 4.78/1.97  tff(c_3939, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_3226, c_6])).
% 4.78/1.97  tff(c_4496, plain, (![A_420, B_421, D_422]: (r2_hidden('#skF_8'(A_420, B_421, k2_zfmisc_1(A_420, B_421), D_422), B_421) | ~r2_hidden(D_422, k2_zfmisc_1(A_420, B_421)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.78/1.97  tff(c_3228, plain, (![A_9]: (r1_xboole_0(A_9, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_3226, c_80])).
% 4.78/1.97  tff(c_3229, plain, (![A_8]: (k3_xboole_0(A_8, '#skF_12')='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_3226, c_3226, c_8])).
% 4.78/1.97  tff(c_3956, plain, (![A_371, B_372, C_373]: (~r1_xboole_0(A_371, B_372) | ~r2_hidden(C_373, k3_xboole_0(A_371, B_372)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.78/1.97  tff(c_3963, plain, (![A_8, C_373]: (~r1_xboole_0(A_8, '#skF_12') | ~r2_hidden(C_373, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_3229, c_3956])).
% 4.78/1.97  tff(c_3966, plain, (![C_373]: (~r2_hidden(C_373, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_3228, c_3963])).
% 4.78/1.97  tff(c_4515, plain, (![D_423, A_424]: (~r2_hidden(D_423, k2_zfmisc_1(A_424, '#skF_12')))), inference(resolution, [status(thm)], [c_4496, c_3966])).
% 4.78/1.97  tff(c_4538, plain, (![A_424]: (k2_zfmisc_1(A_424, '#skF_12')='#skF_12')), inference(resolution, [status(thm)], [c_3939, c_4515])).
% 4.78/1.97  tff(c_3265, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_3226, c_6])).
% 4.78/1.97  tff(c_3884, plain, (![A_360, B_361, D_362]: (r2_hidden('#skF_7'(A_360, B_361, k2_zfmisc_1(A_360, B_361), D_362), A_360) | ~r2_hidden(D_362, k2_zfmisc_1(A_360, B_361)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.78/1.97  tff(c_3283, plain, (![A_313, B_314, C_315]: (~r1_xboole_0(A_313, B_314) | ~r2_hidden(C_315, k3_xboole_0(A_313, B_314)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.78/1.97  tff(c_3290, plain, (![A_8, C_315]: (~r1_xboole_0(A_8, '#skF_12') | ~r2_hidden(C_315, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_3229, c_3283])).
% 4.78/1.97  tff(c_3293, plain, (![C_315]: (~r2_hidden(C_315, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_3228, c_3290])).
% 4.78/1.97  tff(c_3899, plain, (![D_363, B_364]: (~r2_hidden(D_363, k2_zfmisc_1('#skF_12', B_364)))), inference(resolution, [status(thm)], [c_3884, c_3293])).
% 4.78/1.97  tff(c_3919, plain, (![B_364]: (k2_zfmisc_1('#skF_12', B_364)='#skF_12')), inference(resolution, [status(thm)], [c_3265, c_3899])).
% 4.78/1.97  tff(c_52, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.78/1.97  tff(c_3251, plain, ('#skF_10'='#skF_12' | '#skF_9'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_3226, c_3226, c_3226, c_52])).
% 4.78/1.97  tff(c_3252, plain, ('#skF_9'='#skF_12'), inference(splitLeft, [status(thm)], [c_3251])).
% 4.78/1.97  tff(c_3225, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_50])).
% 4.78/1.97  tff(c_3249, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_3226, c_3225])).
% 4.78/1.97  tff(c_3253, plain, (k2_zfmisc_1('#skF_12', '#skF_10')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_3252, c_3249])).
% 4.78/1.97  tff(c_3923, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3919, c_3253])).
% 4.78/1.97  tff(c_3924, plain, ('#skF_10'='#skF_12'), inference(splitRight, [status(thm)], [c_3251])).
% 4.78/1.97  tff(c_3926, plain, (k2_zfmisc_1('#skF_9', '#skF_12')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_3924, c_3249])).
% 4.78/1.97  tff(c_4542, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4538, c_3926])).
% 4.78/1.97  tff(c_4544, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_54])).
% 4.78/1.97  tff(c_56, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.78/1.97  tff(c_4578, plain, ('#skF_11'='#skF_10' | '#skF_11'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_4544, c_4544, c_4544, c_56])).
% 4.78/1.97  tff(c_4579, plain, ('#skF_11'='#skF_9'), inference(splitLeft, [status(thm)], [c_4578])).
% 4.78/1.97  tff(c_4585, plain, (k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_4579, c_4544])).
% 4.78/1.97  tff(c_4615, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_4585, c_6])).
% 4.78/1.97  tff(c_5429, plain, (![A_491, B_492, D_493]: (r2_hidden('#skF_7'(A_491, B_492, k2_zfmisc_1(A_491, B_492), D_493), A_491) | ~r2_hidden(D_493, k2_zfmisc_1(A_491, B_492)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.78/1.97  tff(c_4545, plain, (![A_9]: (r1_xboole_0(A_9, '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_4544, c_80])).
% 4.78/1.97  tff(c_4584, plain, (![A_9]: (r1_xboole_0(A_9, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_4579, c_4545])).
% 4.78/1.97  tff(c_4546, plain, (![A_8]: (k3_xboole_0(A_8, '#skF_11')='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_4544, c_4544, c_8])).
% 4.78/1.97  tff(c_4582, plain, (![A_8]: (k3_xboole_0(A_8, '#skF_9')='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_4579, c_4579, c_4546])).
% 4.78/1.97  tff(c_4770, plain, (![A_443, B_444, C_445]: (~r1_xboole_0(A_443, B_444) | ~r2_hidden(C_445, k3_xboole_0(A_443, B_444)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.78/1.97  tff(c_4783, plain, (![A_8, C_445]: (~r1_xboole_0(A_8, '#skF_9') | ~r2_hidden(C_445, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_4582, c_4770])).
% 4.78/1.97  tff(c_4788, plain, (![C_445]: (~r2_hidden(C_445, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_4584, c_4783])).
% 4.78/1.97  tff(c_5444, plain, (![D_494, B_495]: (~r2_hidden(D_494, k2_zfmisc_1('#skF_9', B_495)))), inference(resolution, [status(thm)], [c_5429, c_4788])).
% 4.78/1.97  tff(c_5464, plain, (![B_495]: (k2_zfmisc_1('#skF_9', B_495)='#skF_9')), inference(resolution, [status(thm)], [c_4615, c_5444])).
% 4.78/1.97  tff(c_4543, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 4.78/1.97  tff(c_4553, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_4544, c_4543])).
% 4.78/1.97  tff(c_4583, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_4579, c_4553])).
% 4.78/1.97  tff(c_5468, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5464, c_4583])).
% 4.78/1.97  tff(c_5469, plain, ('#skF_11'='#skF_10'), inference(splitRight, [status(thm)], [c_4578])).
% 4.78/1.97  tff(c_5475, plain, (k1_xboole_0='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_5469, c_4544])).
% 4.78/1.97  tff(c_5510, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_5475, c_6])).
% 4.78/1.97  tff(c_6128, plain, (![A_558, B_559, D_560]: (r2_hidden('#skF_8'(A_558, B_559, k2_zfmisc_1(A_558, B_559), D_560), B_559) | ~r2_hidden(D_560, k2_zfmisc_1(A_558, B_559)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.78/1.97  tff(c_5474, plain, (![A_9]: (r1_xboole_0(A_9, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_5469, c_4545])).
% 4.78/1.97  tff(c_5472, plain, (![A_8]: (k3_xboole_0(A_8, '#skF_10')='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_5469, c_5469, c_4546])).
% 4.78/1.97  tff(c_5529, plain, (![A_504, B_505, C_506]: (~r1_xboole_0(A_504, B_505) | ~r2_hidden(C_506, k3_xboole_0(A_504, B_505)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.78/1.97  tff(c_5536, plain, (![A_8, C_506]: (~r1_xboole_0(A_8, '#skF_10') | ~r2_hidden(C_506, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_5472, c_5529])).
% 4.78/1.97  tff(c_5539, plain, (![C_506]: (~r2_hidden(C_506, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_5474, c_5536])).
% 4.78/1.97  tff(c_6152, plain, (![D_561, A_562]: (~r2_hidden(D_561, k2_zfmisc_1(A_562, '#skF_10')))), inference(resolution, [status(thm)], [c_6128, c_5539])).
% 4.78/1.97  tff(c_6180, plain, (![A_562]: (k2_zfmisc_1(A_562, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_5510, c_6152])).
% 4.78/1.97  tff(c_5473, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_5469, c_4553])).
% 4.78/1.97  tff(c_6184, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6180, c_5473])).
% 4.78/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.78/1.97  
% 4.78/1.97  Inference rules
% 4.78/1.97  ----------------------
% 4.78/1.97  #Ref     : 0
% 4.78/1.97  #Sup     : 1382
% 4.78/1.97  #Fact    : 0
% 4.78/1.97  #Define  : 0
% 4.78/1.97  #Split   : 13
% 4.78/1.97  #Chain   : 0
% 4.78/1.97  #Close   : 0
% 4.78/1.97  
% 4.78/1.97  Ordering : KBO
% 4.78/1.97  
% 4.78/1.97  Simplification rules
% 4.78/1.97  ----------------------
% 4.78/1.97  #Subsume      : 151
% 4.78/1.97  #Demod        : 941
% 4.78/1.97  #Tautology    : 917
% 4.78/1.97  #SimpNegUnit  : 64
% 4.78/1.97  #BackRed      : 91
% 4.78/1.97  
% 4.78/1.97  #Partial instantiations: 0
% 4.78/1.97  #Strategies tried      : 1
% 4.78/1.97  
% 4.78/1.97  Timing (in seconds)
% 4.78/1.97  ----------------------
% 4.78/1.97  Preprocessing        : 0.33
% 4.78/1.98  Parsing              : 0.17
% 4.78/1.98  CNF conversion       : 0.03
% 4.78/1.98  Main loop            : 0.78
% 4.78/1.98  Inferencing          : 0.30
% 4.78/1.98  Reduction            : 0.26
% 4.78/1.98  Demodulation         : 0.18
% 4.78/1.98  BG Simplification    : 0.03
% 4.78/1.98  Subsumption          : 0.12
% 4.78/1.98  Abstraction          : 0.04
% 4.78/1.98  MUC search           : 0.00
% 4.78/1.98  Cooper               : 0.00
% 4.78/1.98  Total                : 1.18
% 4.78/1.98  Index Insertion      : 0.00
% 4.78/1.98  Index Deletion       : 0.00
% 4.78/1.98  Index Matching       : 0.00
% 4.78/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
