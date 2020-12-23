%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:11 EST 2020

% Result     : Theorem 3.68s
% Output     : CNFRefutation 3.99s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 268 expanded)
%              Number of leaves         :   39 ( 101 expanded)
%              Depth                    :   13
%              Number of atoms          :  150 ( 545 expanded)
%              Number of equality atoms :   59 ( 332 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_126,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_82,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_76,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_60,plain,
    ( k1_tarski('#skF_4') != '#skF_6'
    | k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_87,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_58,plain,
    ( k1_xboole_0 != '#skF_6'
    | k1_tarski('#skF_4') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_69,plain,(
    k1_tarski('#skF_4') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_704,plain,(
    ! [B_137,A_138] :
      ( k3_xboole_0(B_137,k1_tarski(A_138)) = k1_tarski(A_138)
      | ~ r2_hidden(A_138,B_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_64,plain,(
    k2_xboole_0('#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_74,plain,(
    ! [A_69,B_70] : r1_tarski(A_69,k2_xboole_0(A_69,B_70)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_77,plain,(
    r1_tarski('#skF_5',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_74])).

tff(c_126,plain,(
    ! [A_75,B_76] :
      ( k3_xboole_0(A_75,B_76) = A_75
      | ~ r1_tarski(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_136,plain,(
    k3_xboole_0('#skF_5',k1_tarski('#skF_4')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_77,c_126])).

tff(c_723,plain,
    ( k1_tarski('#skF_4') = '#skF_5'
    | ~ r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_704,c_136])).

tff(c_765,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_723])).

tff(c_52,plain,(
    ! [A_59,B_60] :
      ( r1_xboole_0(k1_tarski(A_59),B_60)
      | r2_hidden(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_396,plain,(
    ! [A_115,B_116,C_117] :
      ( ~ r1_xboole_0(A_115,B_116)
      | ~ r2_hidden(C_117,k3_xboole_0(A_115,B_116)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_816,plain,(
    ! [A_145,B_146] :
      ( ~ r1_xboole_0(A_145,B_146)
      | v1_xboole_0(k3_xboole_0(A_145,B_146)) ) ),
    inference(resolution,[status(thm)],[c_6,c_396])).

tff(c_879,plain,(
    ! [B_148,A_149] :
      ( ~ r1_xboole_0(B_148,A_149)
      | v1_xboole_0(k3_xboole_0(A_149,B_148)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_816])).

tff(c_908,plain,
    ( ~ r1_xboole_0(k1_tarski('#skF_4'),'#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_879])).

tff(c_923,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_908])).

tff(c_929,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_923])).

tff(c_935,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_765,c_929])).

tff(c_936,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_908])).

tff(c_18,plain,(
    ! [A_14] :
      ( k1_xboole_0 = A_14
      | ~ v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_992,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_936,c_18])).

tff(c_1000,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_992])).

tff(c_1001,plain,(
    k1_tarski('#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_2'(A_7,B_8),A_7)
      | r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1093,plain,(
    ! [A_162,B_163] :
      ( k3_xboole_0(A_162,B_163) = A_162
      | ~ r1_tarski(A_162,B_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1107,plain,(
    k3_xboole_0('#skF_5',k1_tarski('#skF_4')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_77,c_1093])).

tff(c_1002,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( r1_xboole_0(A_12,B_13)
      | k3_xboole_0(A_12,B_13) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1153,plain,(
    ! [A_12,B_13] :
      ( r1_xboole_0(A_12,B_13)
      | k3_xboole_0(A_12,B_13) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1002,c_16])).

tff(c_1241,plain,(
    ! [A_180,B_181,C_182] :
      ( ~ r1_xboole_0(A_180,B_181)
      | ~ r2_hidden(C_182,k3_xboole_0(A_180,B_181)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1247,plain,(
    ! [C_182] :
      ( ~ r1_xboole_0('#skF_5',k1_tarski('#skF_4'))
      | ~ r2_hidden(C_182,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1107,c_1241])).

tff(c_1318,plain,(
    ~ r1_xboole_0('#skF_5',k1_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1247])).

tff(c_1321,plain,(
    k3_xboole_0('#skF_5',k1_tarski('#skF_4')) != '#skF_5' ),
    inference(resolution,[status(thm)],[c_1153,c_1318])).

tff(c_1325,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1107,c_1321])).

tff(c_1328,plain,(
    ! [C_192] : ~ r2_hidden(C_192,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_1247])).

tff(c_1341,plain,(
    ! [B_193] : r1_tarski('#skF_5',B_193) ),
    inference(resolution,[status(thm)],[c_12,c_1328])).

tff(c_32,plain,(
    ! [A_25,B_26] :
      ( k2_xboole_0(A_25,B_26) = B_26
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1351,plain,(
    ! [B_193] : k2_xboole_0('#skF_5',B_193) = B_193 ),
    inference(resolution,[status(thm)],[c_1341,c_32])).

tff(c_1359,plain,(
    k1_tarski('#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1351,c_64])).

tff(c_1361,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1001,c_1359])).

tff(c_1363,plain,(
    k1_tarski('#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_62,plain,
    ( k1_tarski('#skF_4') != '#skF_6'
    | k1_tarski('#skF_4') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1423,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1363,c_1363,c_62])).

tff(c_28,plain,(
    ! [B_21] : r1_tarski(B_21,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1369,plain,(
    k2_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1363,c_64])).

tff(c_1764,plain,(
    ! [A_235,C_236,B_237] :
      ( r1_tarski(A_235,k2_xboole_0(C_236,B_237))
      | ~ r1_tarski(A_235,B_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1786,plain,(
    ! [A_239] :
      ( r1_tarski(A_239,'#skF_5')
      | ~ r1_tarski(A_239,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1369,c_1764])).

tff(c_34,plain,(
    ! [A_27,B_28] :
      ( k3_xboole_0(A_27,B_28) = A_27
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1795,plain,(
    ! [A_240] :
      ( k3_xboole_0(A_240,'#skF_5') = A_240
      | ~ r1_tarski(A_240,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1786,c_34])).

tff(c_1800,plain,(
    k3_xboole_0('#skF_6','#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_28,c_1795])).

tff(c_1472,plain,(
    ! [A_207,B_208] :
      ( r1_xboole_0(k1_tarski(A_207),B_208)
      | r2_hidden(A_207,B_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1475,plain,(
    ! [B_208] :
      ( r1_xboole_0('#skF_5',B_208)
      | r2_hidden('#skF_4',B_208) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1363,c_1472])).

tff(c_2633,plain,(
    ! [B_285,A_286] :
      ( k3_xboole_0(B_285,k1_tarski(A_286)) = k1_tarski(A_286)
      | ~ r2_hidden(A_286,B_285) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2695,plain,(
    ! [B_285] :
      ( k3_xboole_0(B_285,'#skF_5') = k1_tarski('#skF_4')
      | ~ r2_hidden('#skF_4',B_285) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1363,c_2633])).

tff(c_2708,plain,(
    ! [B_289] :
      ( k3_xboole_0(B_289,'#skF_5') = '#skF_5'
      | ~ r2_hidden('#skF_4',B_289) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1363,c_2695])).

tff(c_2722,plain,(
    ! [B_290] :
      ( k3_xboole_0(B_290,'#skF_5') = '#skF_5'
      | r1_xboole_0('#skF_5',B_290) ) ),
    inference(resolution,[status(thm)],[c_1475,c_2708])).

tff(c_1362,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1868,plain,(
    ! [A_244] :
      ( k2_xboole_0(A_244,'#skF_5') = '#skF_5'
      | ~ r1_tarski(A_244,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1786,c_32])).

tff(c_1873,plain,(
    k2_xboole_0('#skF_6','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_28,c_1868])).

tff(c_36,plain,(
    ! [A_29,B_30] : r1_tarski(A_29,k2_xboole_0(A_29,B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1883,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1873,c_36])).

tff(c_2346,plain,(
    ! [C_272,B_273,A_274] :
      ( r2_hidden(C_272,B_273)
      | ~ r2_hidden(C_272,A_274)
      | ~ r1_tarski(A_274,B_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2433,plain,(
    ! [B_277,B_278] :
      ( r2_hidden('#skF_4',B_277)
      | ~ r1_tarski(B_278,B_277)
      | r1_xboole_0('#skF_5',B_278) ) ),
    inference(resolution,[status(thm)],[c_1475,c_2346])).

tff(c_2450,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | r1_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_1883,c_2433])).

tff(c_2455,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_2450])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = k1_xboole_0
      | ~ r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2459,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2455,c_14])).

tff(c_2481,plain,(
    k3_xboole_0('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2459,c_2])).

tff(c_2510,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1800,c_2481])).

tff(c_2512,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1362,c_2510])).

tff(c_2514,plain,(
    ~ r1_xboole_0('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_2450])).

tff(c_2725,plain,(
    k3_xboole_0('#skF_6','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_2722,c_2514])).

tff(c_2744,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1800,c_2725])).

tff(c_2746,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1423,c_2744])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:11:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.68/1.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.68/1.68  
% 3.68/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.68/1.68  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 3.68/1.68  
% 3.68/1.68  %Foreground sorts:
% 3.68/1.68  
% 3.68/1.68  
% 3.68/1.68  %Background operators:
% 3.68/1.68  
% 3.68/1.68  
% 3.68/1.68  %Foreground operators:
% 3.68/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.68/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.68/1.68  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.68/1.68  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.68/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.68/1.68  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.68/1.68  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.68/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.68/1.68  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.68/1.68  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.68/1.68  tff('#skF_5', type, '#skF_5': $i).
% 3.68/1.68  tff('#skF_6', type, '#skF_6': $i).
% 3.68/1.68  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.68/1.68  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.68/1.68  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.68/1.68  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.68/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.68/1.68  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.68/1.68  tff('#skF_4', type, '#skF_4': $i).
% 3.68/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.68/1.68  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.68/1.68  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.68/1.68  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.68/1.68  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.68/1.68  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.68/1.68  
% 3.99/1.70  tff(f_126, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.99/1.70  tff(f_105, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 3.99/1.70  tff(f_82, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.99/1.70  tff(f_80, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.99/1.70  tff(f_101, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.99/1.70  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.99/1.70  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.99/1.70  tff(f_62, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.99/1.70  tff(f_48, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.99/1.70  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.99/1.70  tff(f_44, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.99/1.70  tff(f_76, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.99/1.70  tff(f_68, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.99/1.70  tff(f_72, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 3.99/1.70  tff(c_60, plain, (k1_tarski('#skF_4')!='#skF_6' | k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.99/1.70  tff(c_87, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_60])).
% 3.99/1.70  tff(c_58, plain, (k1_xboole_0!='#skF_6' | k1_tarski('#skF_4')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.99/1.70  tff(c_69, plain, (k1_tarski('#skF_4')!='#skF_5'), inference(splitLeft, [status(thm)], [c_58])).
% 3.99/1.70  tff(c_704, plain, (![B_137, A_138]: (k3_xboole_0(B_137, k1_tarski(A_138))=k1_tarski(A_138) | ~r2_hidden(A_138, B_137))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.99/1.70  tff(c_64, plain, (k2_xboole_0('#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.99/1.70  tff(c_74, plain, (![A_69, B_70]: (r1_tarski(A_69, k2_xboole_0(A_69, B_70)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.99/1.70  tff(c_77, plain, (r1_tarski('#skF_5', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_74])).
% 3.99/1.70  tff(c_126, plain, (![A_75, B_76]: (k3_xboole_0(A_75, B_76)=A_75 | ~r1_tarski(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.99/1.70  tff(c_136, plain, (k3_xboole_0('#skF_5', k1_tarski('#skF_4'))='#skF_5'), inference(resolution, [status(thm)], [c_77, c_126])).
% 3.99/1.70  tff(c_723, plain, (k1_tarski('#skF_4')='#skF_5' | ~r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_704, c_136])).
% 3.99/1.70  tff(c_765, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_69, c_723])).
% 3.99/1.70  tff(c_52, plain, (![A_59, B_60]: (r1_xboole_0(k1_tarski(A_59), B_60) | r2_hidden(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.99/1.70  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.99/1.70  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.99/1.70  tff(c_396, plain, (![A_115, B_116, C_117]: (~r1_xboole_0(A_115, B_116) | ~r2_hidden(C_117, k3_xboole_0(A_115, B_116)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.99/1.70  tff(c_816, plain, (![A_145, B_146]: (~r1_xboole_0(A_145, B_146) | v1_xboole_0(k3_xboole_0(A_145, B_146)))), inference(resolution, [status(thm)], [c_6, c_396])).
% 3.99/1.70  tff(c_879, plain, (![B_148, A_149]: (~r1_xboole_0(B_148, A_149) | v1_xboole_0(k3_xboole_0(A_149, B_148)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_816])).
% 3.99/1.70  tff(c_908, plain, (~r1_xboole_0(k1_tarski('#skF_4'), '#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_136, c_879])).
% 3.99/1.70  tff(c_923, plain, (~r1_xboole_0(k1_tarski('#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_908])).
% 3.99/1.70  tff(c_929, plain, (r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_52, c_923])).
% 3.99/1.70  tff(c_935, plain, $false, inference(negUnitSimplification, [status(thm)], [c_765, c_929])).
% 3.99/1.70  tff(c_936, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_908])).
% 3.99/1.70  tff(c_18, plain, (![A_14]: (k1_xboole_0=A_14 | ~v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.99/1.70  tff(c_992, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_936, c_18])).
% 3.99/1.70  tff(c_1000, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87, c_992])).
% 3.99/1.70  tff(c_1001, plain, (k1_tarski('#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_60])).
% 3.99/1.70  tff(c_12, plain, (![A_7, B_8]: (r2_hidden('#skF_2'(A_7, B_8), A_7) | r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.99/1.70  tff(c_1093, plain, (![A_162, B_163]: (k3_xboole_0(A_162, B_163)=A_162 | ~r1_tarski(A_162, B_163))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.99/1.70  tff(c_1107, plain, (k3_xboole_0('#skF_5', k1_tarski('#skF_4'))='#skF_5'), inference(resolution, [status(thm)], [c_77, c_1093])).
% 3.99/1.70  tff(c_1002, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_60])).
% 3.99/1.70  tff(c_16, plain, (![A_12, B_13]: (r1_xboole_0(A_12, B_13) | k3_xboole_0(A_12, B_13)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.99/1.70  tff(c_1153, plain, (![A_12, B_13]: (r1_xboole_0(A_12, B_13) | k3_xboole_0(A_12, B_13)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1002, c_16])).
% 3.99/1.70  tff(c_1241, plain, (![A_180, B_181, C_182]: (~r1_xboole_0(A_180, B_181) | ~r2_hidden(C_182, k3_xboole_0(A_180, B_181)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.99/1.70  tff(c_1247, plain, (![C_182]: (~r1_xboole_0('#skF_5', k1_tarski('#skF_4')) | ~r2_hidden(C_182, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1107, c_1241])).
% 3.99/1.70  tff(c_1318, plain, (~r1_xboole_0('#skF_5', k1_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_1247])).
% 3.99/1.70  tff(c_1321, plain, (k3_xboole_0('#skF_5', k1_tarski('#skF_4'))!='#skF_5'), inference(resolution, [status(thm)], [c_1153, c_1318])).
% 3.99/1.70  tff(c_1325, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1107, c_1321])).
% 3.99/1.70  tff(c_1328, plain, (![C_192]: (~r2_hidden(C_192, '#skF_5'))), inference(splitRight, [status(thm)], [c_1247])).
% 3.99/1.70  tff(c_1341, plain, (![B_193]: (r1_tarski('#skF_5', B_193))), inference(resolution, [status(thm)], [c_12, c_1328])).
% 3.99/1.70  tff(c_32, plain, (![A_25, B_26]: (k2_xboole_0(A_25, B_26)=B_26 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.99/1.70  tff(c_1351, plain, (![B_193]: (k2_xboole_0('#skF_5', B_193)=B_193)), inference(resolution, [status(thm)], [c_1341, c_32])).
% 3.99/1.70  tff(c_1359, plain, (k1_tarski('#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1351, c_64])).
% 3.99/1.70  tff(c_1361, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1001, c_1359])).
% 3.99/1.70  tff(c_1363, plain, (k1_tarski('#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_58])).
% 3.99/1.70  tff(c_62, plain, (k1_tarski('#skF_4')!='#skF_6' | k1_tarski('#skF_4')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.99/1.70  tff(c_1423, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1363, c_1363, c_62])).
% 3.99/1.70  tff(c_28, plain, (![B_21]: (r1_tarski(B_21, B_21))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.99/1.70  tff(c_1369, plain, (k2_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1363, c_64])).
% 3.99/1.70  tff(c_1764, plain, (![A_235, C_236, B_237]: (r1_tarski(A_235, k2_xboole_0(C_236, B_237)) | ~r1_tarski(A_235, B_237))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.99/1.70  tff(c_1786, plain, (![A_239]: (r1_tarski(A_239, '#skF_5') | ~r1_tarski(A_239, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1369, c_1764])).
% 3.99/1.70  tff(c_34, plain, (![A_27, B_28]: (k3_xboole_0(A_27, B_28)=A_27 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.99/1.70  tff(c_1795, plain, (![A_240]: (k3_xboole_0(A_240, '#skF_5')=A_240 | ~r1_tarski(A_240, '#skF_6'))), inference(resolution, [status(thm)], [c_1786, c_34])).
% 3.99/1.70  tff(c_1800, plain, (k3_xboole_0('#skF_6', '#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_28, c_1795])).
% 3.99/1.70  tff(c_1472, plain, (![A_207, B_208]: (r1_xboole_0(k1_tarski(A_207), B_208) | r2_hidden(A_207, B_208))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.99/1.70  tff(c_1475, plain, (![B_208]: (r1_xboole_0('#skF_5', B_208) | r2_hidden('#skF_4', B_208))), inference(superposition, [status(thm), theory('equality')], [c_1363, c_1472])).
% 3.99/1.70  tff(c_2633, plain, (![B_285, A_286]: (k3_xboole_0(B_285, k1_tarski(A_286))=k1_tarski(A_286) | ~r2_hidden(A_286, B_285))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.99/1.70  tff(c_2695, plain, (![B_285]: (k3_xboole_0(B_285, '#skF_5')=k1_tarski('#skF_4') | ~r2_hidden('#skF_4', B_285))), inference(superposition, [status(thm), theory('equality')], [c_1363, c_2633])).
% 3.99/1.70  tff(c_2708, plain, (![B_289]: (k3_xboole_0(B_289, '#skF_5')='#skF_5' | ~r2_hidden('#skF_4', B_289))), inference(demodulation, [status(thm), theory('equality')], [c_1363, c_2695])).
% 3.99/1.70  tff(c_2722, plain, (![B_290]: (k3_xboole_0(B_290, '#skF_5')='#skF_5' | r1_xboole_0('#skF_5', B_290))), inference(resolution, [status(thm)], [c_1475, c_2708])).
% 3.99/1.70  tff(c_1362, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_58])).
% 3.99/1.70  tff(c_1868, plain, (![A_244]: (k2_xboole_0(A_244, '#skF_5')='#skF_5' | ~r1_tarski(A_244, '#skF_6'))), inference(resolution, [status(thm)], [c_1786, c_32])).
% 3.99/1.70  tff(c_1873, plain, (k2_xboole_0('#skF_6', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_28, c_1868])).
% 3.99/1.70  tff(c_36, plain, (![A_29, B_30]: (r1_tarski(A_29, k2_xboole_0(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.99/1.70  tff(c_1883, plain, (r1_tarski('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1873, c_36])).
% 3.99/1.70  tff(c_2346, plain, (![C_272, B_273, A_274]: (r2_hidden(C_272, B_273) | ~r2_hidden(C_272, A_274) | ~r1_tarski(A_274, B_273))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.99/1.70  tff(c_2433, plain, (![B_277, B_278]: (r2_hidden('#skF_4', B_277) | ~r1_tarski(B_278, B_277) | r1_xboole_0('#skF_5', B_278))), inference(resolution, [status(thm)], [c_1475, c_2346])).
% 3.99/1.70  tff(c_2450, plain, (r2_hidden('#skF_4', '#skF_5') | r1_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_1883, c_2433])).
% 3.99/1.70  tff(c_2455, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_2450])).
% 3.99/1.70  tff(c_14, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=k1_xboole_0 | ~r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.99/1.70  tff(c_2459, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_2455, c_14])).
% 3.99/1.70  tff(c_2481, plain, (k3_xboole_0('#skF_6', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2459, c_2])).
% 3.99/1.70  tff(c_2510, plain, (k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1800, c_2481])).
% 3.99/1.70  tff(c_2512, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1362, c_2510])).
% 3.99/1.70  tff(c_2514, plain, (~r1_xboole_0('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_2450])).
% 3.99/1.70  tff(c_2725, plain, (k3_xboole_0('#skF_6', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_2722, c_2514])).
% 3.99/1.70  tff(c_2744, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1800, c_2725])).
% 3.99/1.70  tff(c_2746, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1423, c_2744])).
% 3.99/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.99/1.70  
% 3.99/1.70  Inference rules
% 3.99/1.70  ----------------------
% 3.99/1.70  #Ref     : 2
% 3.99/1.70  #Sup     : 654
% 3.99/1.70  #Fact    : 0
% 3.99/1.70  #Define  : 0
% 3.99/1.70  #Split   : 10
% 3.99/1.70  #Chain   : 0
% 3.99/1.70  #Close   : 0
% 3.99/1.70  
% 3.99/1.70  Ordering : KBO
% 3.99/1.70  
% 3.99/1.70  Simplification rules
% 3.99/1.70  ----------------------
% 3.99/1.70  #Subsume      : 165
% 3.99/1.70  #Demod        : 92
% 3.99/1.70  #Tautology    : 251
% 3.99/1.70  #SimpNegUnit  : 32
% 3.99/1.70  #BackRed      : 11
% 3.99/1.70  
% 3.99/1.70  #Partial instantiations: 0
% 3.99/1.70  #Strategies tried      : 1
% 3.99/1.70  
% 3.99/1.70  Timing (in seconds)
% 3.99/1.70  ----------------------
% 3.99/1.70  Preprocessing        : 0.34
% 3.99/1.70  Parsing              : 0.18
% 3.99/1.70  CNF conversion       : 0.02
% 3.99/1.70  Main loop            : 0.56
% 3.99/1.70  Inferencing          : 0.20
% 3.99/1.70  Reduction            : 0.18
% 3.99/1.70  Demodulation         : 0.13
% 3.99/1.70  BG Simplification    : 0.03
% 3.99/1.70  Subsumption          : 0.10
% 3.99/1.70  Abstraction          : 0.03
% 3.99/1.70  MUC search           : 0.00
% 3.99/1.70  Cooper               : 0.00
% 3.99/1.70  Total                : 0.94
% 3.99/1.70  Index Insertion      : 0.00
% 3.99/1.70  Index Deletion       : 0.00
% 3.99/1.70  Index Matching       : 0.00
% 3.99/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
