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
% DateTime   : Thu Dec  3 09:55:05 EST 2020

% Result     : Theorem 5.90s
% Output     : CNFRefutation 5.90s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 717 expanded)
%              Number of leaves         :   32 ( 252 expanded)
%              Depth                    :   15
%              Number of atoms          :  171 (1598 expanded)
%              Number of equality atoms :   11 ( 126 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_3 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_112,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_97,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_74,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_72,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

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

tff(c_52,plain,(
    r1_xboole_0('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_107,plain,(
    ! [B_46,A_47] :
      ( r1_xboole_0(B_46,A_47)
      | ~ r1_xboole_0(A_47,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_110,plain,(
    r1_xboole_0('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_52,c_107])).

tff(c_604,plain,(
    ! [A_146,C_147,B_148] :
      ( ~ r1_xboole_0(A_146,C_147)
      | ~ r1_xboole_0(A_146,B_148)
      | r1_xboole_0(A_146,k2_xboole_0(B_148,C_147)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( r1_xboole_0(B_9,A_8)
      | ~ r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_881,plain,(
    ! [B_175,C_176,A_177] :
      ( r1_xboole_0(k2_xboole_0(B_175,C_176),A_177)
      | ~ r1_xboole_0(A_177,C_176)
      | ~ r1_xboole_0(A_177,B_175) ) ),
    inference(resolution,[status(thm)],[c_604,c_10])).

tff(c_50,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_6','#skF_8'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_896,plain,
    ( ~ r1_xboole_0('#skF_7','#skF_8')
    | ~ r1_xboole_0('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_881,c_50])).

tff(c_903,plain,(
    ~ r1_xboole_0('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_896])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_427,plain,(
    ! [A_116,B_117] :
      ( r2_hidden('#skF_3'(A_116,B_117),k3_xboole_0(A_116,B_117))
      | r1_xboole_0(A_116,B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_441,plain,(
    ! [B_2,A_1] :
      ( r2_hidden('#skF_3'(B_2,A_1),k3_xboole_0(A_1,B_2))
      | r1_xboole_0(B_2,A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_427])).

tff(c_34,plain,(
    ! [C_31] : r2_hidden(C_31,k1_tarski(C_31)) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_131,plain,(
    ! [A_55,B_56] : k4_xboole_0(A_55,k4_xboole_0(A_55,B_56)) = k3_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_22,plain,(
    ! [A_20,B_21] : r1_tarski(k4_xboole_0(A_20,B_21),A_20) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_155,plain,(
    ! [A_59,B_60] : r1_tarski(k3_xboole_0(A_59,B_60),A_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_22])).

tff(c_158,plain,(
    ! [B_2,A_1] : r1_tarski(k3_xboole_0(B_2,A_1),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_155])).

tff(c_54,plain,(
    r2_hidden('#skF_9','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_56,plain,(
    r1_tarski(k3_xboole_0('#skF_6','#skF_7'),k1_tarski('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_215,plain,(
    ! [C_77,B_78,A_79] :
      ( r2_hidden(C_77,B_78)
      | ~ r2_hidden(C_77,A_79)
      | ~ r1_tarski(A_79,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_657,plain,(
    ! [A_151,B_152,B_153] :
      ( r2_hidden('#skF_1'(A_151,B_152),B_153)
      | ~ r1_tarski(A_151,B_153)
      | r1_tarski(A_151,B_152) ) ),
    inference(resolution,[status(thm)],[c_8,c_215])).

tff(c_32,plain,(
    ! [C_31,A_27] :
      ( C_31 = A_27
      | ~ r2_hidden(C_31,k1_tarski(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_3228,plain,(
    ! [A_391,A_392,B_393] :
      ( A_391 = '#skF_1'(A_392,B_393)
      | ~ r1_tarski(A_392,k1_tarski(A_391))
      | r1_tarski(A_392,B_393) ) ),
    inference(resolution,[status(thm)],[c_657,c_32])).

tff(c_3400,plain,(
    ! [B_399] :
      ( '#skF_1'(k3_xboole_0('#skF_6','#skF_7'),B_399) = '#skF_9'
      | r1_tarski(k3_xboole_0('#skF_6','#skF_7'),B_399) ) ),
    inference(resolution,[status(thm)],[c_56,c_3228])).

tff(c_226,plain,(
    ! [A_3,B_4,B_78] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_78)
      | ~ r1_tarski(A_3,B_78)
      | r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_215])).

tff(c_324,plain,(
    ! [A_98,B_99,C_100] :
      ( ~ r1_xboole_0(A_98,B_99)
      | ~ r2_hidden(C_100,B_99)
      | ~ r2_hidden(C_100,A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_336,plain,(
    ! [C_100] :
      ( ~ r2_hidden(C_100,'#skF_7')
      | ~ r2_hidden(C_100,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_52,c_324])).

tff(c_694,plain,(
    ! [A_154,B_155] :
      ( ~ r2_hidden('#skF_1'(A_154,B_155),'#skF_8')
      | ~ r1_tarski(A_154,'#skF_7')
      | r1_tarski(A_154,B_155) ) ),
    inference(resolution,[status(thm)],[c_657,c_336])).

tff(c_709,plain,(
    ! [A_156,B_157] :
      ( ~ r1_tarski(A_156,'#skF_7')
      | ~ r1_tarski(A_156,'#skF_8')
      | r1_tarski(A_156,B_157) ) ),
    inference(resolution,[status(thm)],[c_226,c_694])).

tff(c_735,plain,(
    ! [B_2,B_157] :
      ( ~ r1_tarski(k3_xboole_0(B_2,'#skF_7'),'#skF_8')
      | r1_tarski(k3_xboole_0(B_2,'#skF_7'),B_157) ) ),
    inference(resolution,[status(thm)],[c_158,c_709])).

tff(c_3454,plain,(
    ! [B_157] :
      ( r1_tarski(k3_xboole_0('#skF_6','#skF_7'),B_157)
      | '#skF_1'(k3_xboole_0('#skF_6','#skF_7'),'#skF_8') = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_3400,c_735])).

tff(c_3629,plain,(
    '#skF_1'(k3_xboole_0('#skF_6','#skF_7'),'#skF_8') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_3454])).

tff(c_688,plain,(
    ! [A_151,B_152] :
      ( ~ r2_hidden('#skF_1'(A_151,B_152),'#skF_8')
      | ~ r1_tarski(A_151,'#skF_7')
      | r1_tarski(A_151,B_152) ) ),
    inference(resolution,[status(thm)],[c_657,c_336])).

tff(c_3633,plain,
    ( ~ r2_hidden('#skF_9','#skF_8')
    | ~ r1_tarski(k3_xboole_0('#skF_6','#skF_7'),'#skF_7')
    | r1_tarski(k3_xboole_0('#skF_6','#skF_7'),'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_3629,c_688])).

tff(c_3646,plain,(
    r1_tarski(k3_xboole_0('#skF_6','#skF_7'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_54,c_3633])).

tff(c_140,plain,(
    ! [A_55,B_56] : r1_tarski(k3_xboole_0(A_55,B_56),A_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_22])).

tff(c_774,plain,(
    ! [B_163,B_164] :
      ( ~ r1_tarski(k3_xboole_0('#skF_7',B_163),'#skF_8')
      | r1_tarski(k3_xboole_0('#skF_7',B_163),B_164) ) ),
    inference(resolution,[status(thm)],[c_140,c_709])).

tff(c_786,plain,(
    ! [B_2,B_164] :
      ( ~ r1_tarski(k3_xboole_0(B_2,'#skF_7'),'#skF_8')
      | r1_tarski(k3_xboole_0('#skF_7',B_2),B_164) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_774])).

tff(c_3651,plain,(
    ! [B_164] : r1_tarski(k3_xboole_0('#skF_7','#skF_6'),B_164) ),
    inference(resolution,[status(thm)],[c_3646,c_786])).

tff(c_3657,plain,(
    ! [B_164] : r1_tarski(k3_xboole_0('#skF_6','#skF_7'),B_164) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_3651])).

tff(c_4,plain,(
    ! [C_7,B_4,A_3] :
      ( r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1264,plain,(
    ! [A_210,B_211,B_212] :
      ( r2_hidden('#skF_3'(A_210,B_211),B_212)
      | ~ r1_tarski(k3_xboole_0(A_210,B_211),B_212)
      | r1_xboole_0(A_210,B_211) ) ),
    inference(resolution,[status(thm)],[c_427,c_4])).

tff(c_20,plain,(
    ! [A_15,B_16,C_19] :
      ( ~ r1_xboole_0(A_15,B_16)
      | ~ r2_hidden(C_19,k3_xboole_0(A_15,B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3933,plain,(
    ! [A_423,B_424,A_425,B_426] :
      ( ~ r1_xboole_0(A_423,B_424)
      | ~ r1_tarski(k3_xboole_0(A_425,B_426),k3_xboole_0(A_423,B_424))
      | r1_xboole_0(A_425,B_426) ) ),
    inference(resolution,[status(thm)],[c_1264,c_20])).

tff(c_3990,plain,(
    ! [A_423,B_424] :
      ( ~ r1_xboole_0(A_423,B_424)
      | r1_xboole_0('#skF_6','#skF_7') ) ),
    inference(resolution,[status(thm)],[c_3657,c_3933])).

tff(c_4002,plain,(
    ! [A_423,B_424] : ~ r1_xboole_0(A_423,B_424) ),
    inference(splitLeft,[status(thm)],[c_3990])).

tff(c_3665,plain,(
    ! [B_416] : r1_tarski(k3_xboole_0('#skF_6','#skF_7'),B_416) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_3651])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( r2_hidden('#skF_2'(A_10,B_11),A_10)
      | r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_904,plain,(
    ! [A_178,B_179,B_180] :
      ( r2_hidden('#skF_2'(A_178,B_179),B_180)
      | ~ r1_tarski(A_178,B_180)
      | r1_xboole_0(A_178,B_179) ) ),
    inference(resolution,[status(thm)],[c_16,c_215])).

tff(c_936,plain,(
    ! [A_15,B_16,A_178,B_179] :
      ( ~ r1_xboole_0(A_15,B_16)
      | ~ r1_tarski(A_178,k3_xboole_0(A_15,B_16))
      | r1_xboole_0(A_178,B_179) ) ),
    inference(resolution,[status(thm)],[c_904,c_20])).

tff(c_3710,plain,(
    ! [A_15,B_16,B_179] :
      ( ~ r1_xboole_0(A_15,B_16)
      | r1_xboole_0(k3_xboole_0('#skF_6','#skF_7'),B_179) ) ),
    inference(resolution,[status(thm)],[c_3665,c_936])).

tff(c_3775,plain,(
    ! [A_15,B_16] : ~ r1_xboole_0(A_15,B_16) ),
    inference(splitLeft,[status(thm)],[c_3710])).

tff(c_738,plain,(
    ! [B_158,B_159] :
      ( ~ r1_tarski(k3_xboole_0(B_158,'#skF_7'),'#skF_8')
      | r1_tarski(k3_xboole_0(B_158,'#skF_7'),B_159) ) ),
    inference(resolution,[status(thm)],[c_158,c_709])).

tff(c_756,plain,(
    ! [B_159] : r1_tarski(k3_xboole_0('#skF_8','#skF_7'),B_159) ),
    inference(resolution,[status(thm)],[c_140,c_738])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( r2_hidden('#skF_2'(A_10,B_11),B_11)
      | r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1118,plain,(
    ! [A_203,B_204,B_205] :
      ( r2_hidden('#skF_2'(A_203,B_204),B_205)
      | ~ r1_tarski(B_204,B_205)
      | r1_xboole_0(A_203,B_204) ) ),
    inference(resolution,[status(thm)],[c_14,c_215])).

tff(c_1455,plain,(
    ! [A_227,B_228,B_229,A_230] :
      ( ~ r1_xboole_0(A_227,B_228)
      | ~ r1_tarski(B_229,k3_xboole_0(A_227,B_228))
      | r1_xboole_0(A_230,B_229) ) ),
    inference(resolution,[status(thm)],[c_1118,c_20])).

tff(c_1484,plain,(
    ! [A_227,B_228,A_230] :
      ( ~ r1_xboole_0(A_227,B_228)
      | r1_xboole_0(A_230,k3_xboole_0('#skF_8','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_756,c_1455])).

tff(c_1493,plain,(
    ! [A_227,B_228] : ~ r1_xboole_0(A_227,B_228) ),
    inference(splitLeft,[status(thm)],[c_1484])).

tff(c_1533,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1493,c_110])).

tff(c_1535,plain,(
    ! [A_232] : r1_xboole_0(A_232,k3_xboole_0('#skF_8','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1484])).

tff(c_1541,plain,(
    ! [A_232] : r1_xboole_0(k3_xboole_0('#skF_8','#skF_7'),A_232) ),
    inference(resolution,[status(thm)],[c_1535,c_10])).

tff(c_3845,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3775,c_1541])).

tff(c_3849,plain,(
    ! [B_420] : r1_xboole_0(k3_xboole_0('#skF_6','#skF_7'),B_420) ),
    inference(splitRight,[status(thm)],[c_3710])).

tff(c_3875,plain,(
    ! [B_420] : r1_xboole_0(B_420,k3_xboole_0('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_3849,c_10])).

tff(c_4071,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4002,c_3875])).

tff(c_4072,plain,(
    r1_xboole_0('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_3990])).

tff(c_4080,plain,(
    r1_xboole_0('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_4072,c_10])).

tff(c_4087,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_903,c_4080])).

tff(c_4093,plain,(
    ! [B_429] : r1_tarski(k3_xboole_0('#skF_6','#skF_7'),B_429) ),
    inference(splitRight,[status(thm)],[c_3454])).

tff(c_4138,plain,(
    ! [A_15,B_16,B_179] :
      ( ~ r1_xboole_0(A_15,B_16)
      | r1_xboole_0(k3_xboole_0('#skF_6','#skF_7'),B_179) ) ),
    inference(resolution,[status(thm)],[c_4093,c_936])).

tff(c_4156,plain,(
    ! [A_15,B_16] : ~ r1_xboole_0(A_15,B_16) ),
    inference(splitLeft,[status(thm)],[c_4138])).

tff(c_4226,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4156,c_1541])).

tff(c_4230,plain,(
    ! [B_430] : r1_xboole_0(k3_xboole_0('#skF_6','#skF_7'),B_430) ),
    inference(splitRight,[status(thm)],[c_4138])).

tff(c_12,plain,(
    ! [A_10,B_11,C_14] :
      ( ~ r1_xboole_0(A_10,B_11)
      | ~ r2_hidden(C_14,B_11)
      | ~ r2_hidden(C_14,A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4360,plain,(
    ! [C_436,B_437] :
      ( ~ r2_hidden(C_436,B_437)
      | ~ r2_hidden(C_436,k3_xboole_0('#skF_6','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_4230,c_12])).

tff(c_4406,plain,(
    ! [C_438] : ~ r2_hidden(C_438,k3_xboole_0('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_34,c_4360])).

tff(c_4438,plain,(
    r1_xboole_0('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_441,c_4406])).

tff(c_4469,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_903,c_4438])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:59:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.90/2.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.90/2.13  
% 5.90/2.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.90/2.13  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_3 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 5.90/2.13  
% 5.90/2.13  %Foreground sorts:
% 5.90/2.13  
% 5.90/2.13  
% 5.90/2.13  %Background operators:
% 5.90/2.13  
% 5.90/2.13  
% 5.90/2.13  %Foreground operators:
% 5.90/2.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.90/2.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.90/2.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.90/2.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.90/2.13  tff('#skF_7', type, '#skF_7': $i).
% 5.90/2.13  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.90/2.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.90/2.13  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.90/2.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.90/2.13  tff('#skF_6', type, '#skF_6': $i).
% 5.90/2.13  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.90/2.13  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.90/2.13  tff('#skF_9', type, '#skF_9': $i).
% 5.90/2.13  tff('#skF_8', type, '#skF_8': $i).
% 5.90/2.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.90/2.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.90/2.13  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.90/2.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.90/2.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.90/2.13  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.90/2.13  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.90/2.13  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.90/2.13  
% 5.90/2.15  tff(f_112, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 5.90/2.15  tff(f_38, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 5.90/2.15  tff(f_90, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 5.90/2.15  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.90/2.15  tff(f_70, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.90/2.15  tff(f_97, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 5.90/2.15  tff(f_74, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.90/2.15  tff(f_72, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.90/2.15  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.90/2.15  tff(f_56, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.90/2.15  tff(c_52, plain, (r1_xboole_0('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.90/2.15  tff(c_107, plain, (![B_46, A_47]: (r1_xboole_0(B_46, A_47) | ~r1_xboole_0(A_47, B_46))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.90/2.15  tff(c_110, plain, (r1_xboole_0('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_52, c_107])).
% 5.90/2.15  tff(c_604, plain, (![A_146, C_147, B_148]: (~r1_xboole_0(A_146, C_147) | ~r1_xboole_0(A_146, B_148) | r1_xboole_0(A_146, k2_xboole_0(B_148, C_147)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.90/2.15  tff(c_10, plain, (![B_9, A_8]: (r1_xboole_0(B_9, A_8) | ~r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.90/2.15  tff(c_881, plain, (![B_175, C_176, A_177]: (r1_xboole_0(k2_xboole_0(B_175, C_176), A_177) | ~r1_xboole_0(A_177, C_176) | ~r1_xboole_0(A_177, B_175))), inference(resolution, [status(thm)], [c_604, c_10])).
% 5.90/2.15  tff(c_50, plain, (~r1_xboole_0(k2_xboole_0('#skF_6', '#skF_8'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.90/2.15  tff(c_896, plain, (~r1_xboole_0('#skF_7', '#skF_8') | ~r1_xboole_0('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_881, c_50])).
% 5.90/2.15  tff(c_903, plain, (~r1_xboole_0('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_896])).
% 5.90/2.15  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.90/2.15  tff(c_427, plain, (![A_116, B_117]: (r2_hidden('#skF_3'(A_116, B_117), k3_xboole_0(A_116, B_117)) | r1_xboole_0(A_116, B_117))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.90/2.15  tff(c_441, plain, (![B_2, A_1]: (r2_hidden('#skF_3'(B_2, A_1), k3_xboole_0(A_1, B_2)) | r1_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_427])).
% 5.90/2.15  tff(c_34, plain, (![C_31]: (r2_hidden(C_31, k1_tarski(C_31)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.90/2.15  tff(c_131, plain, (![A_55, B_56]: (k4_xboole_0(A_55, k4_xboole_0(A_55, B_56))=k3_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.90/2.15  tff(c_22, plain, (![A_20, B_21]: (r1_tarski(k4_xboole_0(A_20, B_21), A_20))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.90/2.15  tff(c_155, plain, (![A_59, B_60]: (r1_tarski(k3_xboole_0(A_59, B_60), A_59))), inference(superposition, [status(thm), theory('equality')], [c_131, c_22])).
% 5.90/2.15  tff(c_158, plain, (![B_2, A_1]: (r1_tarski(k3_xboole_0(B_2, A_1), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_155])).
% 5.90/2.15  tff(c_54, plain, (r2_hidden('#skF_9', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.90/2.15  tff(c_56, plain, (r1_tarski(k3_xboole_0('#skF_6', '#skF_7'), k1_tarski('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.90/2.15  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.90/2.15  tff(c_215, plain, (![C_77, B_78, A_79]: (r2_hidden(C_77, B_78) | ~r2_hidden(C_77, A_79) | ~r1_tarski(A_79, B_78))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.90/2.15  tff(c_657, plain, (![A_151, B_152, B_153]: (r2_hidden('#skF_1'(A_151, B_152), B_153) | ~r1_tarski(A_151, B_153) | r1_tarski(A_151, B_152))), inference(resolution, [status(thm)], [c_8, c_215])).
% 5.90/2.15  tff(c_32, plain, (![C_31, A_27]: (C_31=A_27 | ~r2_hidden(C_31, k1_tarski(A_27)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.90/2.15  tff(c_3228, plain, (![A_391, A_392, B_393]: (A_391='#skF_1'(A_392, B_393) | ~r1_tarski(A_392, k1_tarski(A_391)) | r1_tarski(A_392, B_393))), inference(resolution, [status(thm)], [c_657, c_32])).
% 5.90/2.15  tff(c_3400, plain, (![B_399]: ('#skF_1'(k3_xboole_0('#skF_6', '#skF_7'), B_399)='#skF_9' | r1_tarski(k3_xboole_0('#skF_6', '#skF_7'), B_399))), inference(resolution, [status(thm)], [c_56, c_3228])).
% 5.90/2.15  tff(c_226, plain, (![A_3, B_4, B_78]: (r2_hidden('#skF_1'(A_3, B_4), B_78) | ~r1_tarski(A_3, B_78) | r1_tarski(A_3, B_4))), inference(resolution, [status(thm)], [c_8, c_215])).
% 5.90/2.15  tff(c_324, plain, (![A_98, B_99, C_100]: (~r1_xboole_0(A_98, B_99) | ~r2_hidden(C_100, B_99) | ~r2_hidden(C_100, A_98))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.90/2.15  tff(c_336, plain, (![C_100]: (~r2_hidden(C_100, '#skF_7') | ~r2_hidden(C_100, '#skF_8'))), inference(resolution, [status(thm)], [c_52, c_324])).
% 5.90/2.15  tff(c_694, plain, (![A_154, B_155]: (~r2_hidden('#skF_1'(A_154, B_155), '#skF_8') | ~r1_tarski(A_154, '#skF_7') | r1_tarski(A_154, B_155))), inference(resolution, [status(thm)], [c_657, c_336])).
% 5.90/2.15  tff(c_709, plain, (![A_156, B_157]: (~r1_tarski(A_156, '#skF_7') | ~r1_tarski(A_156, '#skF_8') | r1_tarski(A_156, B_157))), inference(resolution, [status(thm)], [c_226, c_694])).
% 5.90/2.15  tff(c_735, plain, (![B_2, B_157]: (~r1_tarski(k3_xboole_0(B_2, '#skF_7'), '#skF_8') | r1_tarski(k3_xboole_0(B_2, '#skF_7'), B_157))), inference(resolution, [status(thm)], [c_158, c_709])).
% 5.90/2.15  tff(c_3454, plain, (![B_157]: (r1_tarski(k3_xboole_0('#skF_6', '#skF_7'), B_157) | '#skF_1'(k3_xboole_0('#skF_6', '#skF_7'), '#skF_8')='#skF_9')), inference(resolution, [status(thm)], [c_3400, c_735])).
% 5.90/2.15  tff(c_3629, plain, ('#skF_1'(k3_xboole_0('#skF_6', '#skF_7'), '#skF_8')='#skF_9'), inference(splitLeft, [status(thm)], [c_3454])).
% 5.90/2.15  tff(c_688, plain, (![A_151, B_152]: (~r2_hidden('#skF_1'(A_151, B_152), '#skF_8') | ~r1_tarski(A_151, '#skF_7') | r1_tarski(A_151, B_152))), inference(resolution, [status(thm)], [c_657, c_336])).
% 5.90/2.15  tff(c_3633, plain, (~r2_hidden('#skF_9', '#skF_8') | ~r1_tarski(k3_xboole_0('#skF_6', '#skF_7'), '#skF_7') | r1_tarski(k3_xboole_0('#skF_6', '#skF_7'), '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_3629, c_688])).
% 5.90/2.15  tff(c_3646, plain, (r1_tarski(k3_xboole_0('#skF_6', '#skF_7'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_158, c_54, c_3633])).
% 5.90/2.15  tff(c_140, plain, (![A_55, B_56]: (r1_tarski(k3_xboole_0(A_55, B_56), A_55))), inference(superposition, [status(thm), theory('equality')], [c_131, c_22])).
% 5.90/2.15  tff(c_774, plain, (![B_163, B_164]: (~r1_tarski(k3_xboole_0('#skF_7', B_163), '#skF_8') | r1_tarski(k3_xboole_0('#skF_7', B_163), B_164))), inference(resolution, [status(thm)], [c_140, c_709])).
% 5.90/2.15  tff(c_786, plain, (![B_2, B_164]: (~r1_tarski(k3_xboole_0(B_2, '#skF_7'), '#skF_8') | r1_tarski(k3_xboole_0('#skF_7', B_2), B_164))), inference(superposition, [status(thm), theory('equality')], [c_2, c_774])).
% 5.90/2.15  tff(c_3651, plain, (![B_164]: (r1_tarski(k3_xboole_0('#skF_7', '#skF_6'), B_164))), inference(resolution, [status(thm)], [c_3646, c_786])).
% 5.90/2.15  tff(c_3657, plain, (![B_164]: (r1_tarski(k3_xboole_0('#skF_6', '#skF_7'), B_164))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_3651])).
% 5.90/2.15  tff(c_4, plain, (![C_7, B_4, A_3]: (r2_hidden(C_7, B_4) | ~r2_hidden(C_7, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.90/2.15  tff(c_1264, plain, (![A_210, B_211, B_212]: (r2_hidden('#skF_3'(A_210, B_211), B_212) | ~r1_tarski(k3_xboole_0(A_210, B_211), B_212) | r1_xboole_0(A_210, B_211))), inference(resolution, [status(thm)], [c_427, c_4])).
% 5.90/2.15  tff(c_20, plain, (![A_15, B_16, C_19]: (~r1_xboole_0(A_15, B_16) | ~r2_hidden(C_19, k3_xboole_0(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.90/2.15  tff(c_3933, plain, (![A_423, B_424, A_425, B_426]: (~r1_xboole_0(A_423, B_424) | ~r1_tarski(k3_xboole_0(A_425, B_426), k3_xboole_0(A_423, B_424)) | r1_xboole_0(A_425, B_426))), inference(resolution, [status(thm)], [c_1264, c_20])).
% 5.90/2.15  tff(c_3990, plain, (![A_423, B_424]: (~r1_xboole_0(A_423, B_424) | r1_xboole_0('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_3657, c_3933])).
% 5.90/2.15  tff(c_4002, plain, (![A_423, B_424]: (~r1_xboole_0(A_423, B_424))), inference(splitLeft, [status(thm)], [c_3990])).
% 5.90/2.15  tff(c_3665, plain, (![B_416]: (r1_tarski(k3_xboole_0('#skF_6', '#skF_7'), B_416))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_3651])).
% 5.90/2.15  tff(c_16, plain, (![A_10, B_11]: (r2_hidden('#skF_2'(A_10, B_11), A_10) | r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.90/2.15  tff(c_904, plain, (![A_178, B_179, B_180]: (r2_hidden('#skF_2'(A_178, B_179), B_180) | ~r1_tarski(A_178, B_180) | r1_xboole_0(A_178, B_179))), inference(resolution, [status(thm)], [c_16, c_215])).
% 5.90/2.15  tff(c_936, plain, (![A_15, B_16, A_178, B_179]: (~r1_xboole_0(A_15, B_16) | ~r1_tarski(A_178, k3_xboole_0(A_15, B_16)) | r1_xboole_0(A_178, B_179))), inference(resolution, [status(thm)], [c_904, c_20])).
% 5.90/2.15  tff(c_3710, plain, (![A_15, B_16, B_179]: (~r1_xboole_0(A_15, B_16) | r1_xboole_0(k3_xboole_0('#skF_6', '#skF_7'), B_179))), inference(resolution, [status(thm)], [c_3665, c_936])).
% 5.90/2.15  tff(c_3775, plain, (![A_15, B_16]: (~r1_xboole_0(A_15, B_16))), inference(splitLeft, [status(thm)], [c_3710])).
% 5.90/2.15  tff(c_738, plain, (![B_158, B_159]: (~r1_tarski(k3_xboole_0(B_158, '#skF_7'), '#skF_8') | r1_tarski(k3_xboole_0(B_158, '#skF_7'), B_159))), inference(resolution, [status(thm)], [c_158, c_709])).
% 5.90/2.15  tff(c_756, plain, (![B_159]: (r1_tarski(k3_xboole_0('#skF_8', '#skF_7'), B_159))), inference(resolution, [status(thm)], [c_140, c_738])).
% 5.90/2.15  tff(c_14, plain, (![A_10, B_11]: (r2_hidden('#skF_2'(A_10, B_11), B_11) | r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.90/2.15  tff(c_1118, plain, (![A_203, B_204, B_205]: (r2_hidden('#skF_2'(A_203, B_204), B_205) | ~r1_tarski(B_204, B_205) | r1_xboole_0(A_203, B_204))), inference(resolution, [status(thm)], [c_14, c_215])).
% 5.90/2.15  tff(c_1455, plain, (![A_227, B_228, B_229, A_230]: (~r1_xboole_0(A_227, B_228) | ~r1_tarski(B_229, k3_xboole_0(A_227, B_228)) | r1_xboole_0(A_230, B_229))), inference(resolution, [status(thm)], [c_1118, c_20])).
% 5.90/2.15  tff(c_1484, plain, (![A_227, B_228, A_230]: (~r1_xboole_0(A_227, B_228) | r1_xboole_0(A_230, k3_xboole_0('#skF_8', '#skF_7')))), inference(resolution, [status(thm)], [c_756, c_1455])).
% 5.90/2.15  tff(c_1493, plain, (![A_227, B_228]: (~r1_xboole_0(A_227, B_228))), inference(splitLeft, [status(thm)], [c_1484])).
% 5.90/2.15  tff(c_1533, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1493, c_110])).
% 5.90/2.15  tff(c_1535, plain, (![A_232]: (r1_xboole_0(A_232, k3_xboole_0('#skF_8', '#skF_7')))), inference(splitRight, [status(thm)], [c_1484])).
% 5.90/2.15  tff(c_1541, plain, (![A_232]: (r1_xboole_0(k3_xboole_0('#skF_8', '#skF_7'), A_232))), inference(resolution, [status(thm)], [c_1535, c_10])).
% 5.90/2.15  tff(c_3845, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3775, c_1541])).
% 5.90/2.15  tff(c_3849, plain, (![B_420]: (r1_xboole_0(k3_xboole_0('#skF_6', '#skF_7'), B_420))), inference(splitRight, [status(thm)], [c_3710])).
% 5.90/2.15  tff(c_3875, plain, (![B_420]: (r1_xboole_0(B_420, k3_xboole_0('#skF_6', '#skF_7')))), inference(resolution, [status(thm)], [c_3849, c_10])).
% 5.90/2.15  tff(c_4071, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4002, c_3875])).
% 5.90/2.15  tff(c_4072, plain, (r1_xboole_0('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_3990])).
% 5.90/2.15  tff(c_4080, plain, (r1_xboole_0('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_4072, c_10])).
% 5.90/2.15  tff(c_4087, plain, $false, inference(negUnitSimplification, [status(thm)], [c_903, c_4080])).
% 5.90/2.15  tff(c_4093, plain, (![B_429]: (r1_tarski(k3_xboole_0('#skF_6', '#skF_7'), B_429))), inference(splitRight, [status(thm)], [c_3454])).
% 5.90/2.15  tff(c_4138, plain, (![A_15, B_16, B_179]: (~r1_xboole_0(A_15, B_16) | r1_xboole_0(k3_xboole_0('#skF_6', '#skF_7'), B_179))), inference(resolution, [status(thm)], [c_4093, c_936])).
% 5.90/2.15  tff(c_4156, plain, (![A_15, B_16]: (~r1_xboole_0(A_15, B_16))), inference(splitLeft, [status(thm)], [c_4138])).
% 5.90/2.15  tff(c_4226, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4156, c_1541])).
% 5.90/2.15  tff(c_4230, plain, (![B_430]: (r1_xboole_0(k3_xboole_0('#skF_6', '#skF_7'), B_430))), inference(splitRight, [status(thm)], [c_4138])).
% 5.90/2.15  tff(c_12, plain, (![A_10, B_11, C_14]: (~r1_xboole_0(A_10, B_11) | ~r2_hidden(C_14, B_11) | ~r2_hidden(C_14, A_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.90/2.15  tff(c_4360, plain, (![C_436, B_437]: (~r2_hidden(C_436, B_437) | ~r2_hidden(C_436, k3_xboole_0('#skF_6', '#skF_7')))), inference(resolution, [status(thm)], [c_4230, c_12])).
% 5.90/2.15  tff(c_4406, plain, (![C_438]: (~r2_hidden(C_438, k3_xboole_0('#skF_6', '#skF_7')))), inference(resolution, [status(thm)], [c_34, c_4360])).
% 5.90/2.15  tff(c_4438, plain, (r1_xboole_0('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_441, c_4406])).
% 5.90/2.15  tff(c_4469, plain, $false, inference(negUnitSimplification, [status(thm)], [c_903, c_4438])).
% 5.90/2.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.90/2.15  
% 5.90/2.15  Inference rules
% 5.90/2.15  ----------------------
% 5.90/2.15  #Ref     : 0
% 5.90/2.15  #Sup     : 1039
% 5.90/2.15  #Fact    : 0
% 5.90/2.15  #Define  : 0
% 5.90/2.15  #Split   : 7
% 5.90/2.15  #Chain   : 0
% 5.90/2.15  #Close   : 0
% 5.90/2.15  
% 5.90/2.15  Ordering : KBO
% 5.90/2.15  
% 5.90/2.15  Simplification rules
% 5.90/2.15  ----------------------
% 5.90/2.15  #Subsume      : 616
% 5.90/2.15  #Demod        : 134
% 5.90/2.15  #Tautology    : 161
% 5.90/2.15  #SimpNegUnit  : 252
% 5.90/2.15  #BackRed      : 159
% 5.90/2.15  
% 5.90/2.15  #Partial instantiations: 0
% 5.90/2.15  #Strategies tried      : 1
% 5.90/2.15  
% 5.90/2.15  Timing (in seconds)
% 5.90/2.15  ----------------------
% 5.90/2.16  Preprocessing        : 0.32
% 5.90/2.16  Parsing              : 0.17
% 5.90/2.16  CNF conversion       : 0.02
% 5.90/2.16  Main loop            : 1.07
% 5.90/2.16  Inferencing          : 0.36
% 5.90/2.16  Reduction            : 0.34
% 5.90/2.16  Demodulation         : 0.24
% 5.90/2.16  BG Simplification    : 0.03
% 5.90/2.16  Subsumption          : 0.26
% 5.90/2.16  Abstraction          : 0.05
% 5.90/2.16  MUC search           : 0.00
% 5.90/2.16  Cooper               : 0.00
% 5.90/2.16  Total                : 1.43
% 5.90/2.16  Index Insertion      : 0.00
% 5.90/2.16  Index Deletion       : 0.00
% 5.90/2.16  Index Matching       : 0.00
% 5.90/2.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
