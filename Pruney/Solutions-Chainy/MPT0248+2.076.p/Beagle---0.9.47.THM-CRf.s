%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:14 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 242 expanded)
%              Number of leaves         :   37 (  93 expanded)
%              Depth                    :   11
%              Number of atoms          :  119 ( 409 expanded)
%              Number of equality atoms :   81 ( 368 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_127,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_80,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_106,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_66,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_64,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_78,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_86,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_84,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_82,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(c_66,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_120,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_64,plain,
    ( k1_xboole_0 != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_119,plain,(
    k1_tarski('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_70,plain,(
    k2_xboole_0('#skF_4','#skF_5') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_145,plain,(
    ! [A_73,B_74] : r1_tarski(A_73,k2_xboole_0(A_73,B_74)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_148,plain,(
    r1_tarski('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_145])).

tff(c_313,plain,(
    ! [B_94,A_95] :
      ( k1_tarski(B_94) = A_95
      | k1_xboole_0 = A_95
      | ~ r1_tarski(A_95,k1_tarski(B_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_316,plain,
    ( k1_tarski('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_148,c_313])).

tff(c_331,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_119,c_316])).

tff(c_332,plain,(
    k1_tarski('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_403,plain,(
    ! [B_105,A_106] : k5_xboole_0(B_105,A_106) = k5_xboole_0(A_106,B_105) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_333,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_28,plain,(
    ! [A_21] : k5_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_335,plain,(
    ! [A_21] : k5_xboole_0(A_21,'#skF_4') = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_28])).

tff(c_419,plain,(
    ! [A_106] : k5_xboole_0('#skF_4',A_106) = A_106 ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_335])).

tff(c_26,plain,(
    ! [A_19,B_20] : r1_tarski(k3_xboole_0(A_19,B_20),A_19) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_30,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_337,plain,(
    r1_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_333,c_30])).

tff(c_595,plain,(
    ! [A_132,B_133,C_134] :
      ( ~ r1_xboole_0(A_132,B_133)
      | ~ r2_hidden(C_134,B_133)
      | ~ r2_hidden(C_134,A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_599,plain,(
    ! [C_135] : ~ r2_hidden(C_135,'#skF_4') ),
    inference(resolution,[status(thm)],[c_337,c_595])).

tff(c_683,plain,(
    ! [B_139] : r1_tarski('#skF_4',B_139) ),
    inference(resolution,[status(thm)],[c_8,c_599])).

tff(c_20,plain,(
    ! [B_18,A_17] :
      ( B_18 = A_17
      | ~ r1_tarski(B_18,A_17)
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_778,plain,(
    ! [B_144] :
      ( B_144 = '#skF_4'
      | ~ r1_tarski(B_144,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_683,c_20])).

tff(c_793,plain,(
    ! [B_20] : k3_xboole_0('#skF_4',B_20) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_26,c_778])).

tff(c_714,plain,(
    ! [A_142,B_143] : k5_xboole_0(k5_xboole_0(A_142,B_143),k2_xboole_0(A_142,B_143)) = k3_xboole_0(A_142,B_143) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_766,plain,(
    k5_xboole_0(k5_xboole_0('#skF_4','#skF_5'),k1_tarski('#skF_3')) = k3_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_714])).

tff(c_776,plain,(
    k5_xboole_0('#skF_5',k1_tarski('#skF_3')) = k3_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_419,c_766])).

tff(c_1194,plain,(
    k5_xboole_0('#skF_5',k1_tarski('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_793,c_776])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_38,plain,(
    ! [A_28] : k5_xboole_0(A_28,A_28) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_334,plain,(
    ! [A_28] : k5_xboole_0(A_28,A_28) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_38])).

tff(c_615,plain,(
    ! [A_136,B_137,C_138] : k5_xboole_0(k5_xboole_0(A_136,B_137),C_138) = k5_xboole_0(A_136,k5_xboole_0(B_137,C_138)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_661,plain,(
    ! [A_28,C_138] : k5_xboole_0(A_28,k5_xboole_0(A_28,C_138)) = k5_xboole_0('#skF_4',C_138) ),
    inference(superposition,[status(thm),theory(equality)],[c_334,c_615])).

tff(c_817,plain,(
    ! [A_146,C_147] : k5_xboole_0(A_146,k5_xboole_0(A_146,C_147)) = C_147 ),
    inference(demodulation,[status(thm),theory(equality)],[c_419,c_661])).

tff(c_885,plain,(
    ! [A_148,B_149] : k5_xboole_0(A_148,k5_xboole_0(B_149,A_148)) = B_149 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_817])).

tff(c_863,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_817])).

tff(c_888,plain,(
    ! [B_149,A_148] : k5_xboole_0(k5_xboole_0(B_149,A_148),B_149) = A_148 ),
    inference(superposition,[status(thm),theory(equality)],[c_885,c_863])).

tff(c_1201,plain,(
    k5_xboole_0('#skF_4','#skF_5') = k1_tarski('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1194,c_888])).

tff(c_1216,plain,(
    k1_tarski('#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_419,c_1201])).

tff(c_1218,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_332,c_1216])).

tff(c_1219,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_1220,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_68,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1259,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1220,c_1220,c_68])).

tff(c_1265,plain,(
    ! [B_164,A_165] : k5_xboole_0(B_164,A_165) = k5_xboole_0(A_165,B_164) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1281,plain,(
    ! [A_165] : k5_xboole_0(k1_xboole_0,A_165) = A_165 ),
    inference(superposition,[status(thm),theory(equality)],[c_1265,c_28])).

tff(c_1615,plain,(
    ! [A_202,B_203,C_204] : k5_xboole_0(k5_xboole_0(A_202,B_203),C_204) = k5_xboole_0(A_202,k5_xboole_0(B_203,C_204)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1661,plain,(
    ! [A_28,C_204] : k5_xboole_0(A_28,k5_xboole_0(A_28,C_204)) = k5_xboole_0(k1_xboole_0,C_204) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1615])).

tff(c_1682,plain,(
    ! [A_205,C_206] : k5_xboole_0(A_205,k5_xboole_0(A_205,C_206)) = C_206 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1281,c_1661])).

tff(c_1744,plain,(
    ! [A_207,B_208] : k5_xboole_0(A_207,k5_xboole_0(B_208,A_207)) = B_208 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1682])).

tff(c_1722,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1682])).

tff(c_1747,plain,(
    ! [B_208,A_207] : k5_xboole_0(k5_xboole_0(B_208,A_207),B_208) = A_207 ),
    inference(superposition,[status(thm),theory(equality)],[c_1744,c_1722])).

tff(c_1227,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1220,c_70])).

tff(c_1914,plain,(
    ! [A_211,B_212] : k5_xboole_0(k5_xboole_0(A_211,B_212),k2_xboole_0(A_211,B_212)) = k3_xboole_0(A_211,B_212) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1981,plain,(
    k5_xboole_0(k5_xboole_0('#skF_4','#skF_5'),'#skF_4') = k3_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1227,c_1914])).

tff(c_1994,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1747,c_1981])).

tff(c_1533,plain,(
    ! [B_195,A_196] :
      ( k1_tarski(B_195) = A_196
      | k1_xboole_0 = A_196
      | ~ r1_tarski(A_196,k1_tarski(B_195)) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1544,plain,(
    ! [A_196] :
      ( k1_tarski('#skF_3') = A_196
      | k1_xboole_0 = A_196
      | ~ r1_tarski(A_196,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1220,c_1533])).

tff(c_1555,plain,(
    ! [A_197] :
      ( A_197 = '#skF_4'
      | k1_xboole_0 = A_197
      | ~ r1_tarski(A_197,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1220,c_1544])).

tff(c_1572,plain,(
    ! [B_20] :
      ( k3_xboole_0('#skF_4',B_20) = '#skF_4'
      | k3_xboole_0('#skF_4',B_20) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_1555])).

tff(c_2000,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1994,c_1572])).

tff(c_2009,plain,
    ( '#skF_5' = '#skF_4'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1994,c_2000])).

tff(c_2011,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1219,c_1259,c_2009])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:37:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.52/1.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.64  
% 3.52/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.64  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.52/1.64  
% 3.52/1.64  %Foreground sorts:
% 3.52/1.64  
% 3.52/1.64  
% 3.52/1.64  %Background operators:
% 3.52/1.64  
% 3.52/1.64  
% 3.52/1.64  %Foreground operators:
% 3.52/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.52/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.52/1.64  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.52/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.52/1.64  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.52/1.64  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.52/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.52/1.64  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.52/1.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.52/1.64  tff('#skF_5', type, '#skF_5': $i).
% 3.52/1.64  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.52/1.64  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.52/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.52/1.64  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.52/1.64  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.52/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.52/1.64  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.52/1.64  tff('#skF_4', type, '#skF_4': $i).
% 3.52/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.52/1.64  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.52/1.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.52/1.64  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.52/1.64  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.52/1.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.52/1.64  
% 3.52/1.66  tff(f_127, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.52/1.66  tff(f_80, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.52/1.66  tff(f_106, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.52/1.66  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.52/1.66  tff(f_66, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.52/1.66  tff(f_64, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.52/1.66  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.52/1.66  tff(f_78, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 3.52/1.66  tff(f_56, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.52/1.66  tff(f_62, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.52/1.66  tff(f_86, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 3.52/1.66  tff(f_84, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.52/1.66  tff(f_82, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.52/1.66  tff(c_66, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.52/1.66  tff(c_120, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_66])).
% 3.52/1.66  tff(c_64, plain, (k1_xboole_0!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.52/1.66  tff(c_119, plain, (k1_tarski('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_64])).
% 3.52/1.66  tff(c_70, plain, (k2_xboole_0('#skF_4', '#skF_5')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.52/1.66  tff(c_145, plain, (![A_73, B_74]: (r1_tarski(A_73, k2_xboole_0(A_73, B_74)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.52/1.66  tff(c_148, plain, (r1_tarski('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_145])).
% 3.52/1.66  tff(c_313, plain, (![B_94, A_95]: (k1_tarski(B_94)=A_95 | k1_xboole_0=A_95 | ~r1_tarski(A_95, k1_tarski(B_94)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.52/1.66  tff(c_316, plain, (k1_tarski('#skF_3')='#skF_4' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_148, c_313])).
% 3.52/1.66  tff(c_331, plain, $false, inference(negUnitSimplification, [status(thm)], [c_120, c_119, c_316])).
% 3.52/1.66  tff(c_332, plain, (k1_tarski('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_66])).
% 3.52/1.66  tff(c_403, plain, (![B_105, A_106]: (k5_xboole_0(B_105, A_106)=k5_xboole_0(A_106, B_105))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.52/1.66  tff(c_333, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_66])).
% 3.52/1.66  tff(c_28, plain, (![A_21]: (k5_xboole_0(A_21, k1_xboole_0)=A_21)), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.52/1.66  tff(c_335, plain, (![A_21]: (k5_xboole_0(A_21, '#skF_4')=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_333, c_28])).
% 3.52/1.66  tff(c_419, plain, (![A_106]: (k5_xboole_0('#skF_4', A_106)=A_106)), inference(superposition, [status(thm), theory('equality')], [c_403, c_335])).
% 3.52/1.66  tff(c_26, plain, (![A_19, B_20]: (r1_tarski(k3_xboole_0(A_19, B_20), A_19))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.52/1.66  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.52/1.66  tff(c_30, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.52/1.66  tff(c_337, plain, (r1_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_333, c_333, c_30])).
% 3.52/1.66  tff(c_595, plain, (![A_132, B_133, C_134]: (~r1_xboole_0(A_132, B_133) | ~r2_hidden(C_134, B_133) | ~r2_hidden(C_134, A_132))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.52/1.66  tff(c_599, plain, (![C_135]: (~r2_hidden(C_135, '#skF_4'))), inference(resolution, [status(thm)], [c_337, c_595])).
% 3.52/1.66  tff(c_683, plain, (![B_139]: (r1_tarski('#skF_4', B_139))), inference(resolution, [status(thm)], [c_8, c_599])).
% 3.52/1.66  tff(c_20, plain, (![B_18, A_17]: (B_18=A_17 | ~r1_tarski(B_18, A_17) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.52/1.66  tff(c_778, plain, (![B_144]: (B_144='#skF_4' | ~r1_tarski(B_144, '#skF_4'))), inference(resolution, [status(thm)], [c_683, c_20])).
% 3.52/1.66  tff(c_793, plain, (![B_20]: (k3_xboole_0('#skF_4', B_20)='#skF_4')), inference(resolution, [status(thm)], [c_26, c_778])).
% 3.52/1.66  tff(c_714, plain, (![A_142, B_143]: (k5_xboole_0(k5_xboole_0(A_142, B_143), k2_xboole_0(A_142, B_143))=k3_xboole_0(A_142, B_143))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.52/1.66  tff(c_766, plain, (k5_xboole_0(k5_xboole_0('#skF_4', '#skF_5'), k1_tarski('#skF_3'))=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_70, c_714])).
% 3.52/1.66  tff(c_776, plain, (k5_xboole_0('#skF_5', k1_tarski('#skF_3'))=k3_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_419, c_766])).
% 3.52/1.66  tff(c_1194, plain, (k5_xboole_0('#skF_5', k1_tarski('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_793, c_776])).
% 3.52/1.66  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.52/1.66  tff(c_38, plain, (![A_28]: (k5_xboole_0(A_28, A_28)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.52/1.66  tff(c_334, plain, (![A_28]: (k5_xboole_0(A_28, A_28)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_333, c_38])).
% 3.52/1.66  tff(c_615, plain, (![A_136, B_137, C_138]: (k5_xboole_0(k5_xboole_0(A_136, B_137), C_138)=k5_xboole_0(A_136, k5_xboole_0(B_137, C_138)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.52/1.66  tff(c_661, plain, (![A_28, C_138]: (k5_xboole_0(A_28, k5_xboole_0(A_28, C_138))=k5_xboole_0('#skF_4', C_138))), inference(superposition, [status(thm), theory('equality')], [c_334, c_615])).
% 3.52/1.66  tff(c_817, plain, (![A_146, C_147]: (k5_xboole_0(A_146, k5_xboole_0(A_146, C_147))=C_147)), inference(demodulation, [status(thm), theory('equality')], [c_419, c_661])).
% 3.52/1.66  tff(c_885, plain, (![A_148, B_149]: (k5_xboole_0(A_148, k5_xboole_0(B_149, A_148))=B_149)), inference(superposition, [status(thm), theory('equality')], [c_2, c_817])).
% 3.52/1.66  tff(c_863, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_817])).
% 3.52/1.66  tff(c_888, plain, (![B_149, A_148]: (k5_xboole_0(k5_xboole_0(B_149, A_148), B_149)=A_148)), inference(superposition, [status(thm), theory('equality')], [c_885, c_863])).
% 3.52/1.66  tff(c_1201, plain, (k5_xboole_0('#skF_4', '#skF_5')=k1_tarski('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1194, c_888])).
% 3.52/1.66  tff(c_1216, plain, (k1_tarski('#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_419, c_1201])).
% 3.52/1.66  tff(c_1218, plain, $false, inference(negUnitSimplification, [status(thm)], [c_332, c_1216])).
% 3.52/1.66  tff(c_1219, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_64])).
% 3.52/1.66  tff(c_1220, plain, (k1_tarski('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_64])).
% 3.52/1.66  tff(c_68, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.52/1.66  tff(c_1259, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1220, c_1220, c_68])).
% 3.52/1.66  tff(c_1265, plain, (![B_164, A_165]: (k5_xboole_0(B_164, A_165)=k5_xboole_0(A_165, B_164))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.52/1.66  tff(c_1281, plain, (![A_165]: (k5_xboole_0(k1_xboole_0, A_165)=A_165)), inference(superposition, [status(thm), theory('equality')], [c_1265, c_28])).
% 3.52/1.66  tff(c_1615, plain, (![A_202, B_203, C_204]: (k5_xboole_0(k5_xboole_0(A_202, B_203), C_204)=k5_xboole_0(A_202, k5_xboole_0(B_203, C_204)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.52/1.66  tff(c_1661, plain, (![A_28, C_204]: (k5_xboole_0(A_28, k5_xboole_0(A_28, C_204))=k5_xboole_0(k1_xboole_0, C_204))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1615])).
% 3.52/1.66  tff(c_1682, plain, (![A_205, C_206]: (k5_xboole_0(A_205, k5_xboole_0(A_205, C_206))=C_206)), inference(demodulation, [status(thm), theory('equality')], [c_1281, c_1661])).
% 3.52/1.66  tff(c_1744, plain, (![A_207, B_208]: (k5_xboole_0(A_207, k5_xboole_0(B_208, A_207))=B_208)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1682])).
% 3.52/1.66  tff(c_1722, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1682])).
% 3.52/1.66  tff(c_1747, plain, (![B_208, A_207]: (k5_xboole_0(k5_xboole_0(B_208, A_207), B_208)=A_207)), inference(superposition, [status(thm), theory('equality')], [c_1744, c_1722])).
% 3.52/1.66  tff(c_1227, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1220, c_70])).
% 3.52/1.66  tff(c_1914, plain, (![A_211, B_212]: (k5_xboole_0(k5_xboole_0(A_211, B_212), k2_xboole_0(A_211, B_212))=k3_xboole_0(A_211, B_212))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.52/1.66  tff(c_1981, plain, (k5_xboole_0(k5_xboole_0('#skF_4', '#skF_5'), '#skF_4')=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1227, c_1914])).
% 3.52/1.66  tff(c_1994, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1747, c_1981])).
% 3.52/1.66  tff(c_1533, plain, (![B_195, A_196]: (k1_tarski(B_195)=A_196 | k1_xboole_0=A_196 | ~r1_tarski(A_196, k1_tarski(B_195)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.52/1.66  tff(c_1544, plain, (![A_196]: (k1_tarski('#skF_3')=A_196 | k1_xboole_0=A_196 | ~r1_tarski(A_196, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1220, c_1533])).
% 3.52/1.66  tff(c_1555, plain, (![A_197]: (A_197='#skF_4' | k1_xboole_0=A_197 | ~r1_tarski(A_197, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1220, c_1544])).
% 3.52/1.66  tff(c_1572, plain, (![B_20]: (k3_xboole_0('#skF_4', B_20)='#skF_4' | k3_xboole_0('#skF_4', B_20)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_1555])).
% 3.52/1.66  tff(c_2000, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_1994, c_1572])).
% 3.52/1.66  tff(c_2009, plain, ('#skF_5'='#skF_4' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1994, c_2000])).
% 3.52/1.66  tff(c_2011, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1219, c_1259, c_2009])).
% 3.52/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.66  
% 3.52/1.66  Inference rules
% 3.52/1.66  ----------------------
% 3.52/1.66  #Ref     : 0
% 3.52/1.66  #Sup     : 459
% 3.52/1.66  #Fact    : 1
% 3.52/1.66  #Define  : 0
% 3.52/1.66  #Split   : 3
% 3.52/1.66  #Chain   : 0
% 3.52/1.66  #Close   : 0
% 3.52/1.66  
% 3.52/1.66  Ordering : KBO
% 3.52/1.66  
% 3.52/1.66  Simplification rules
% 3.52/1.66  ----------------------
% 3.52/1.66  #Subsume      : 16
% 3.52/1.66  #Demod        : 186
% 3.52/1.66  #Tautology    : 304
% 3.52/1.66  #SimpNegUnit  : 10
% 3.52/1.66  #BackRed      : 4
% 3.52/1.66  
% 3.52/1.66  #Partial instantiations: 0
% 3.52/1.66  #Strategies tried      : 1
% 3.52/1.66  
% 3.52/1.66  Timing (in seconds)
% 3.52/1.66  ----------------------
% 3.52/1.66  Preprocessing        : 0.36
% 3.52/1.66  Parsing              : 0.20
% 3.52/1.66  CNF conversion       : 0.03
% 3.52/1.66  Main loop            : 0.47
% 3.52/1.66  Inferencing          : 0.17
% 3.52/1.66  Reduction            : 0.17
% 3.52/1.66  Demodulation         : 0.13
% 3.52/1.66  BG Simplification    : 0.03
% 3.52/1.66  Subsumption          : 0.07
% 3.52/1.66  Abstraction          : 0.02
% 3.52/1.66  MUC search           : 0.00
% 3.52/1.66  Cooper               : 0.00
% 3.52/1.66  Total                : 0.87
% 3.52/1.66  Index Insertion      : 0.00
% 3.52/1.66  Index Deletion       : 0.00
% 3.52/1.66  Index Matching       : 0.00
% 3.52/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
