%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:30 EST 2020

% Result     : Theorem 5.05s
% Output     : CNFRefutation 5.37s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 186 expanded)
%              Number of leaves         :   44 (  82 expanded)
%              Depth                    :   15
%              Number of atoms          :   85 ( 198 expanded)
%              Number of equality atoms :   59 ( 136 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_2 > #skF_7 > #skF_4 > #skF_8 > #skF_3 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_112,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_53,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_67,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_63,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_97,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_95,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_99,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_93,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_84,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_80,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_2'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_336,plain,(
    ! [A_118,B_119] : k5_xboole_0(A_118,k3_xboole_0(A_118,B_119)) = k4_xboole_0(A_118,B_119) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_366,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_336])).

tff(c_26,plain,(
    ! [A_26,B_27] : k5_xboole_0(A_26,k4_xboole_0(B_27,A_26)) = k2_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_640,plain,(
    ! [A_142,B_143,C_144] : k5_xboole_0(k5_xboole_0(A_142,B_143),C_144) = k5_xboole_0(A_142,k5_xboole_0(B_143,C_144)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_3376,plain,(
    ! [A_256,C_257] : k5_xboole_0(k4_xboole_0(A_256,A_256),C_257) = k5_xboole_0(A_256,k5_xboole_0(A_256,C_257)) ),
    inference(superposition,[status(thm),theory(equality)],[c_366,c_640])).

tff(c_3406,plain,(
    ! [A_256] : k5_xboole_0(A_256,k5_xboole_0(A_256,k4_xboole_0(A_256,A_256))) = k4_xboole_0(k4_xboole_0(A_256,A_256),k4_xboole_0(A_256,A_256)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3376,c_366])).

tff(c_4019,plain,(
    ! [A_272] : k4_xboole_0(k4_xboole_0(A_272,A_272),k4_xboole_0(A_272,A_272)) = k4_xboole_0(A_272,A_272) ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_4,c_26,c_3406])).

tff(c_22,plain,(
    ! [A_21,B_22] : r1_xboole_0(k4_xboole_0(A_21,B_22),B_22) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4114,plain,(
    ! [A_273] : r1_xboole_0(k4_xboole_0(A_273,A_273),k4_xboole_0(A_273,A_273)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4019,c_22])).

tff(c_262,plain,(
    ! [A_106,B_107,C_108] :
      ( ~ r1_xboole_0(A_106,B_107)
      | ~ r2_hidden(C_108,k3_xboole_0(A_106,B_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_284,plain,(
    ! [A_5,C_108] :
      ( ~ r1_xboole_0(A_5,A_5)
      | ~ r2_hidden(C_108,A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_262])).

tff(c_4164,plain,(
    ! [C_274,A_275] : ~ r2_hidden(C_274,k4_xboole_0(A_275,A_275)) ),
    inference(resolution,[status(thm)],[c_4114,c_284])).

tff(c_4233,plain,(
    ! [A_277] : k4_xboole_0(A_277,A_277) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_4164])).

tff(c_20,plain,(
    ! [A_20] : k5_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_288,plain,(
    ! [A_111,B_112] :
      ( ~ r1_xboole_0(A_111,B_112)
      | k3_xboole_0(A_111,B_112) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_262])).

tff(c_292,plain,(
    ! [A_21,B_22] : k3_xboole_0(k4_xboole_0(A_21,B_22),B_22) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_288])).

tff(c_348,plain,(
    ! [A_21,B_22] : k5_xboole_0(k4_xboole_0(A_21,B_22),k1_xboole_0) = k4_xboole_0(k4_xboole_0(A_21,B_22),B_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_336])).

tff(c_1101,plain,(
    ! [A_164,B_165] : k4_xboole_0(k4_xboole_0(A_164,B_165),B_165) = k4_xboole_0(A_164,B_165) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_348])).

tff(c_1122,plain,(
    ! [B_165,A_164] : k5_xboole_0(B_165,k4_xboole_0(A_164,B_165)) = k2_xboole_0(B_165,k4_xboole_0(A_164,B_165)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1101,c_26])).

tff(c_1147,plain,(
    ! [B_165,A_164] : k2_xboole_0(B_165,k4_xboole_0(A_164,B_165)) = k2_xboole_0(B_165,A_164) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1122])).

tff(c_4250,plain,(
    ! [A_277] : k2_xboole_0(A_277,k1_xboole_0) = k2_xboole_0(A_277,A_277) ),
    inference(superposition,[status(thm),theory(equality)],[c_4233,c_1147])).

tff(c_4282,plain,(
    ! [A_277] : k2_xboole_0(A_277,k1_xboole_0) = A_277 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4250])).

tff(c_68,plain,(
    ! [A_45,B_46] : k1_enumset1(A_45,A_45,B_46) = k2_tarski(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_66,plain,(
    ! [A_44] : k2_tarski(A_44,A_44) = k1_tarski(A_44) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_70,plain,(
    ! [A_47,B_48,C_49] : k2_enumset1(A_47,A_47,B_48,C_49) = k1_enumset1(A_47,B_48,C_49) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1959,plain,(
    ! [A_192,B_193,C_194,D_195] : k2_xboole_0(k1_enumset1(A_192,B_193,C_194),k1_tarski(D_195)) = k2_enumset1(A_192,B_193,C_194,D_195) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1990,plain,(
    ! [A_45,B_46,D_195] : k2_xboole_0(k2_tarski(A_45,B_46),k1_tarski(D_195)) = k2_enumset1(A_45,A_45,B_46,D_195) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_1959])).

tff(c_2828,plain,(
    ! [A_228,B_229,D_230] : k2_xboole_0(k2_tarski(A_228,B_229),k1_tarski(D_230)) = k1_enumset1(A_228,B_229,D_230) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1990])).

tff(c_2859,plain,(
    ! [A_44,D_230] : k2_xboole_0(k1_tarski(A_44),k1_tarski(D_230)) = k1_enumset1(A_44,A_44,D_230) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_2828])).

tff(c_2862,plain,(
    ! [A_44,D_230] : k2_xboole_0(k1_tarski(A_44),k1_tarski(D_230)) = k2_tarski(A_44,D_230) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2859])).

tff(c_4196,plain,(
    ! [A_275] : k4_xboole_0(A_275,A_275) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_4164])).

tff(c_4231,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4196,c_366])).

tff(c_82,plain,(
    r1_tarski(k1_tarski('#skF_7'),k1_tarski('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_182,plain,(
    ! [A_95,B_96] :
      ( k3_xboole_0(A_95,B_96) = A_95
      | ~ r1_tarski(A_95,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_186,plain,(
    k3_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_tarski('#skF_7') ),
    inference(resolution,[status(thm)],[c_82,c_182])).

tff(c_354,plain,(
    k5_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_7')) = k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_336])).

tff(c_4346,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4231,c_354])).

tff(c_4688,plain,(
    k2_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_7')) = k2_xboole_0(k1_tarski('#skF_8'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4346,c_1147])).

tff(c_4712,plain,(
    k2_tarski('#skF_8','#skF_7') = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4282,c_2862,c_4688])).

tff(c_187,plain,(
    ! [A_97,B_98] : k1_enumset1(A_97,A_97,B_98) = k2_tarski(A_97,B_98) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_30,plain,(
    ! [E_34,A_28,B_29] : r2_hidden(E_34,k1_enumset1(A_28,B_29,E_34)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_199,plain,(
    ! [B_98,A_97] : r2_hidden(B_98,k2_tarski(A_97,B_98)) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_30])).

tff(c_4954,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4712,c_199])).

tff(c_52,plain,(
    ! [C_39,A_35] :
      ( C_39 = A_35
      | ~ r2_hidden(C_39,k1_tarski(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_4966,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_4954,c_52])).

tff(c_4970,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_4966])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:31:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.05/2.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.05/2.06  
% 5.05/2.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.05/2.06  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_2 > #skF_7 > #skF_4 > #skF_8 > #skF_3 > #skF_1 > #skF_5
% 5.05/2.06  
% 5.05/2.06  %Foreground sorts:
% 5.05/2.06  
% 5.05/2.06  
% 5.05/2.06  %Background operators:
% 5.05/2.06  
% 5.05/2.06  
% 5.05/2.06  %Foreground operators:
% 5.05/2.06  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 5.05/2.06  tff('#skF_2', type, '#skF_2': $i > $i).
% 5.05/2.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.05/2.06  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.05/2.06  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.05/2.06  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.05/2.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.05/2.06  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.05/2.06  tff('#skF_7', type, '#skF_7': $i).
% 5.05/2.06  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.05/2.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.05/2.06  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.05/2.06  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.05/2.06  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.05/2.06  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.05/2.06  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.05/2.06  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 5.05/2.06  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.05/2.06  tff('#skF_8', type, '#skF_8': $i).
% 5.05/2.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.05/2.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.05/2.06  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.05/2.06  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 5.05/2.06  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.05/2.06  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.05/2.06  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.05/2.06  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.05/2.06  
% 5.37/2.08  tff(f_112, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 5.37/2.08  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 5.37/2.08  tff(f_53, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 5.37/2.08  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.37/2.08  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.37/2.08  tff(f_69, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.37/2.08  tff(f_67, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.37/2.08  tff(f_65, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 5.37/2.08  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.37/2.08  tff(f_63, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 5.37/2.08  tff(f_97, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 5.37/2.08  tff(f_95, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 5.37/2.08  tff(f_99, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 5.37/2.08  tff(f_93, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 5.37/2.08  tff(f_61, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.37/2.08  tff(f_84, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 5.37/2.08  tff(f_91, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 5.37/2.08  tff(c_80, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.37/2.08  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.37/2.08  tff(c_12, plain, (![A_12]: (r2_hidden('#skF_2'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.37/2.08  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.37/2.08  tff(c_336, plain, (![A_118, B_119]: (k5_xboole_0(A_118, k3_xboole_0(A_118, B_119))=k4_xboole_0(A_118, B_119))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.37/2.08  tff(c_366, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_336])).
% 5.37/2.08  tff(c_26, plain, (![A_26, B_27]: (k5_xboole_0(A_26, k4_xboole_0(B_27, A_26))=k2_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.37/2.08  tff(c_640, plain, (![A_142, B_143, C_144]: (k5_xboole_0(k5_xboole_0(A_142, B_143), C_144)=k5_xboole_0(A_142, k5_xboole_0(B_143, C_144)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.37/2.08  tff(c_3376, plain, (![A_256, C_257]: (k5_xboole_0(k4_xboole_0(A_256, A_256), C_257)=k5_xboole_0(A_256, k5_xboole_0(A_256, C_257)))), inference(superposition, [status(thm), theory('equality')], [c_366, c_640])).
% 5.37/2.08  tff(c_3406, plain, (![A_256]: (k5_xboole_0(A_256, k5_xboole_0(A_256, k4_xboole_0(A_256, A_256)))=k4_xboole_0(k4_xboole_0(A_256, A_256), k4_xboole_0(A_256, A_256)))), inference(superposition, [status(thm), theory('equality')], [c_3376, c_366])).
% 5.37/2.08  tff(c_4019, plain, (![A_272]: (k4_xboole_0(k4_xboole_0(A_272, A_272), k4_xboole_0(A_272, A_272))=k4_xboole_0(A_272, A_272))), inference(demodulation, [status(thm), theory('equality')], [c_366, c_4, c_26, c_3406])).
% 5.37/2.08  tff(c_22, plain, (![A_21, B_22]: (r1_xboole_0(k4_xboole_0(A_21, B_22), B_22))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.37/2.08  tff(c_4114, plain, (![A_273]: (r1_xboole_0(k4_xboole_0(A_273, A_273), k4_xboole_0(A_273, A_273)))), inference(superposition, [status(thm), theory('equality')], [c_4019, c_22])).
% 5.37/2.08  tff(c_262, plain, (![A_106, B_107, C_108]: (~r1_xboole_0(A_106, B_107) | ~r2_hidden(C_108, k3_xboole_0(A_106, B_107)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.37/2.08  tff(c_284, plain, (![A_5, C_108]: (~r1_xboole_0(A_5, A_5) | ~r2_hidden(C_108, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_262])).
% 5.37/2.08  tff(c_4164, plain, (![C_274, A_275]: (~r2_hidden(C_274, k4_xboole_0(A_275, A_275)))), inference(resolution, [status(thm)], [c_4114, c_284])).
% 5.37/2.08  tff(c_4233, plain, (![A_277]: (k4_xboole_0(A_277, A_277)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_4164])).
% 5.37/2.08  tff(c_20, plain, (![A_20]: (k5_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.37/2.08  tff(c_288, plain, (![A_111, B_112]: (~r1_xboole_0(A_111, B_112) | k3_xboole_0(A_111, B_112)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_262])).
% 5.37/2.08  tff(c_292, plain, (![A_21, B_22]: (k3_xboole_0(k4_xboole_0(A_21, B_22), B_22)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_288])).
% 5.37/2.08  tff(c_348, plain, (![A_21, B_22]: (k5_xboole_0(k4_xboole_0(A_21, B_22), k1_xboole_0)=k4_xboole_0(k4_xboole_0(A_21, B_22), B_22))), inference(superposition, [status(thm), theory('equality')], [c_292, c_336])).
% 5.37/2.08  tff(c_1101, plain, (![A_164, B_165]: (k4_xboole_0(k4_xboole_0(A_164, B_165), B_165)=k4_xboole_0(A_164, B_165))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_348])).
% 5.37/2.08  tff(c_1122, plain, (![B_165, A_164]: (k5_xboole_0(B_165, k4_xboole_0(A_164, B_165))=k2_xboole_0(B_165, k4_xboole_0(A_164, B_165)))), inference(superposition, [status(thm), theory('equality')], [c_1101, c_26])).
% 5.37/2.08  tff(c_1147, plain, (![B_165, A_164]: (k2_xboole_0(B_165, k4_xboole_0(A_164, B_165))=k2_xboole_0(B_165, A_164))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1122])).
% 5.37/2.08  tff(c_4250, plain, (![A_277]: (k2_xboole_0(A_277, k1_xboole_0)=k2_xboole_0(A_277, A_277))), inference(superposition, [status(thm), theory('equality')], [c_4233, c_1147])).
% 5.37/2.08  tff(c_4282, plain, (![A_277]: (k2_xboole_0(A_277, k1_xboole_0)=A_277)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4250])).
% 5.37/2.08  tff(c_68, plain, (![A_45, B_46]: (k1_enumset1(A_45, A_45, B_46)=k2_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.37/2.08  tff(c_66, plain, (![A_44]: (k2_tarski(A_44, A_44)=k1_tarski(A_44))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.37/2.08  tff(c_70, plain, (![A_47, B_48, C_49]: (k2_enumset1(A_47, A_47, B_48, C_49)=k1_enumset1(A_47, B_48, C_49))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.37/2.08  tff(c_1959, plain, (![A_192, B_193, C_194, D_195]: (k2_xboole_0(k1_enumset1(A_192, B_193, C_194), k1_tarski(D_195))=k2_enumset1(A_192, B_193, C_194, D_195))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.37/2.08  tff(c_1990, plain, (![A_45, B_46, D_195]: (k2_xboole_0(k2_tarski(A_45, B_46), k1_tarski(D_195))=k2_enumset1(A_45, A_45, B_46, D_195))), inference(superposition, [status(thm), theory('equality')], [c_68, c_1959])).
% 5.37/2.08  tff(c_2828, plain, (![A_228, B_229, D_230]: (k2_xboole_0(k2_tarski(A_228, B_229), k1_tarski(D_230))=k1_enumset1(A_228, B_229, D_230))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1990])).
% 5.37/2.08  tff(c_2859, plain, (![A_44, D_230]: (k2_xboole_0(k1_tarski(A_44), k1_tarski(D_230))=k1_enumset1(A_44, A_44, D_230))), inference(superposition, [status(thm), theory('equality')], [c_66, c_2828])).
% 5.37/2.08  tff(c_2862, plain, (![A_44, D_230]: (k2_xboole_0(k1_tarski(A_44), k1_tarski(D_230))=k2_tarski(A_44, D_230))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2859])).
% 5.37/2.08  tff(c_4196, plain, (![A_275]: (k4_xboole_0(A_275, A_275)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_4164])).
% 5.37/2.08  tff(c_4231, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4196, c_366])).
% 5.37/2.08  tff(c_82, plain, (r1_tarski(k1_tarski('#skF_7'), k1_tarski('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.37/2.08  tff(c_182, plain, (![A_95, B_96]: (k3_xboole_0(A_95, B_96)=A_95 | ~r1_tarski(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.37/2.08  tff(c_186, plain, (k3_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_tarski('#skF_7')), inference(resolution, [status(thm)], [c_82, c_182])).
% 5.37/2.08  tff(c_354, plain, (k5_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_7'))=k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_186, c_336])).
% 5.37/2.08  tff(c_4346, plain, (k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4231, c_354])).
% 5.37/2.08  tff(c_4688, plain, (k2_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_7'))=k2_xboole_0(k1_tarski('#skF_8'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4346, c_1147])).
% 5.37/2.08  tff(c_4712, plain, (k2_tarski('#skF_8', '#skF_7')=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4282, c_2862, c_4688])).
% 5.37/2.08  tff(c_187, plain, (![A_97, B_98]: (k1_enumset1(A_97, A_97, B_98)=k2_tarski(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.37/2.08  tff(c_30, plain, (![E_34, A_28, B_29]: (r2_hidden(E_34, k1_enumset1(A_28, B_29, E_34)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.37/2.08  tff(c_199, plain, (![B_98, A_97]: (r2_hidden(B_98, k2_tarski(A_97, B_98)))), inference(superposition, [status(thm), theory('equality')], [c_187, c_30])).
% 5.37/2.08  tff(c_4954, plain, (r2_hidden('#skF_7', k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_4712, c_199])).
% 5.37/2.08  tff(c_52, plain, (![C_39, A_35]: (C_39=A_35 | ~r2_hidden(C_39, k1_tarski(A_35)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.37/2.08  tff(c_4966, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_4954, c_52])).
% 5.37/2.08  tff(c_4970, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_4966])).
% 5.37/2.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.37/2.08  
% 5.37/2.08  Inference rules
% 5.37/2.08  ----------------------
% 5.37/2.08  #Ref     : 0
% 5.37/2.08  #Sup     : 1157
% 5.37/2.08  #Fact    : 0
% 5.37/2.08  #Define  : 0
% 5.37/2.08  #Split   : 2
% 5.37/2.08  #Chain   : 0
% 5.37/2.08  #Close   : 0
% 5.37/2.08  
% 5.37/2.08  Ordering : KBO
% 5.37/2.08  
% 5.37/2.08  Simplification rules
% 5.37/2.08  ----------------------
% 5.37/2.08  #Subsume      : 103
% 5.37/2.08  #Demod        : 1019
% 5.37/2.08  #Tautology    : 732
% 5.37/2.08  #SimpNegUnit  : 32
% 5.37/2.08  #BackRed      : 33
% 5.37/2.08  
% 5.37/2.08  #Partial instantiations: 0
% 5.37/2.08  #Strategies tried      : 1
% 5.37/2.08  
% 5.37/2.08  Timing (in seconds)
% 5.37/2.08  ----------------------
% 5.43/2.08  Preprocessing        : 0.36
% 5.43/2.08  Parsing              : 0.19
% 5.43/2.08  CNF conversion       : 0.03
% 5.43/2.08  Main loop            : 0.90
% 5.43/2.08  Inferencing          : 0.28
% 5.43/2.08  Reduction            : 0.38
% 5.43/2.08  Demodulation         : 0.30
% 5.43/2.08  BG Simplification    : 0.04
% 5.43/2.08  Subsumption          : 0.15
% 5.43/2.08  Abstraction          : 0.04
% 5.43/2.08  MUC search           : 0.00
% 5.43/2.08  Cooper               : 0.00
% 5.43/2.08  Total                : 1.30
% 5.43/2.08  Index Insertion      : 0.00
% 5.43/2.08  Index Deletion       : 0.00
% 5.43/2.08  Index Matching       : 0.00
% 5.43/2.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
