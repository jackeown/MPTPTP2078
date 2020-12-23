%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:36 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 100 expanded)
%              Number of leaves         :   37 (  49 expanded)
%              Depth                    :   17
%              Number of atoms          :   73 ( 101 expanded)
%              Number of equality atoms :   61 (  85 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_56,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_60,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_62,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_64,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_66,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_68,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k1_tarski(H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_52,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_40,plain,(
    ! [A_25,B_26] : k1_enumset1(A_25,A_25,B_26) = k2_tarski(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_38,plain,(
    ! [A_24] : k2_tarski(A_24,A_24) = k1_tarski(A_24) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_42,plain,(
    ! [A_27,B_28,C_29] : k2_enumset1(A_27,A_27,B_28,C_29) = k1_enumset1(A_27,B_28,C_29) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_44,plain,(
    ! [A_30,B_31,C_32,D_33] : k3_enumset1(A_30,A_30,B_31,C_32,D_33) = k2_enumset1(A_30,B_31,C_32,D_33) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_46,plain,(
    ! [D_37,A_34,B_35,C_36,E_38] : k4_enumset1(A_34,A_34,B_35,C_36,D_37,E_38) = k3_enumset1(A_34,B_35,C_36,D_37,E_38) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_48,plain,(
    ! [E_43,F_44,D_42,A_39,C_41,B_40] : k5_enumset1(A_39,A_39,B_40,C_41,D_42,E_43,F_44) = k4_enumset1(A_39,B_40,C_41,D_42,E_43,F_44) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_50,plain,(
    ! [D_48,C_47,A_45,B_46,G_51,E_49,F_50] : k6_enumset1(A_45,A_45,B_46,C_47,D_48,E_49,F_50,G_51) = k5_enumset1(A_45,B_46,C_47,D_48,E_49,F_50,G_51) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_268,plain,(
    ! [H_128,G_129,F_127,A_132,D_133,C_134,E_131,B_130] : k2_xboole_0(k5_enumset1(A_132,B_130,C_134,D_133,E_131,F_127,G_129),k1_tarski(H_128)) = k6_enumset1(A_132,B_130,C_134,D_133,E_131,F_127,G_129,H_128) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_277,plain,(
    ! [H_128,E_43,F_44,D_42,A_39,C_41,B_40] : k6_enumset1(A_39,A_39,B_40,C_41,D_42,E_43,F_44,H_128) = k2_xboole_0(k4_enumset1(A_39,B_40,C_41,D_42,E_43,F_44),k1_tarski(H_128)) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_268])).

tff(c_281,plain,(
    ! [C_137,B_136,E_141,F_140,H_138,D_139,A_135] : k2_xboole_0(k4_enumset1(A_135,B_136,C_137,D_139,E_141,F_140),k1_tarski(H_138)) = k5_enumset1(A_135,B_136,C_137,D_139,E_141,F_140,H_138) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_277])).

tff(c_290,plain,(
    ! [D_37,A_34,B_35,C_36,H_138,E_38] : k5_enumset1(A_34,A_34,B_35,C_36,D_37,E_38,H_138) = k2_xboole_0(k3_enumset1(A_34,B_35,C_36,D_37,E_38),k1_tarski(H_138)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_281])).

tff(c_294,plain,(
    ! [H_146,C_147,E_144,A_142,D_143,B_145] : k2_xboole_0(k3_enumset1(A_142,B_145,C_147,D_143,E_144),k1_tarski(H_146)) = k4_enumset1(A_142,B_145,C_147,D_143,E_144,H_146) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_290])).

tff(c_303,plain,(
    ! [H_146,D_33,A_30,C_32,B_31] : k4_enumset1(A_30,A_30,B_31,C_32,D_33,H_146) = k2_xboole_0(k2_enumset1(A_30,B_31,C_32,D_33),k1_tarski(H_146)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_294])).

tff(c_307,plain,(
    ! [C_148,H_150,B_149,D_152,A_151] : k2_xboole_0(k2_enumset1(A_151,B_149,C_148,D_152),k1_tarski(H_150)) = k3_enumset1(A_151,B_149,C_148,D_152,H_150) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_303])).

tff(c_316,plain,(
    ! [A_27,B_28,C_29,H_150] : k3_enumset1(A_27,A_27,B_28,C_29,H_150) = k2_xboole_0(k1_enumset1(A_27,B_28,C_29),k1_tarski(H_150)) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_307])).

tff(c_321,plain,(
    ! [A_157,B_158,C_159,H_160] : k2_xboole_0(k1_enumset1(A_157,B_158,C_159),k1_tarski(H_160)) = k2_enumset1(A_157,B_158,C_159,H_160) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_316])).

tff(c_330,plain,(
    ! [A_25,B_26,H_160] : k2_xboole_0(k2_tarski(A_25,B_26),k1_tarski(H_160)) = k2_enumset1(A_25,A_25,B_26,H_160) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_321])).

tff(c_334,plain,(
    ! [A_161,B_162,H_163] : k2_xboole_0(k2_tarski(A_161,B_162),k1_tarski(H_163)) = k1_enumset1(A_161,B_162,H_163) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_330])).

tff(c_343,plain,(
    ! [A_24,H_163] : k2_xboole_0(k1_tarski(A_24),k1_tarski(H_163)) = k1_enumset1(A_24,A_24,H_163) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_334])).

tff(c_347,plain,(
    ! [A_164,H_165] : k2_xboole_0(k1_tarski(A_164),k1_tarski(H_165)) = k2_tarski(A_164,H_165) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_343])).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_6] : k5_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_54,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_93,plain,(
    ! [A_64,B_65] :
      ( k3_xboole_0(A_64,B_65) = A_64
      | ~ r1_tarski(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_97,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_93])).

tff(c_140,plain,(
    ! [A_75,B_76] : k5_xboole_0(A_75,k3_xboole_0(A_75,B_76)) = k4_xboole_0(A_75,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_149,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_140])).

tff(c_152,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_149])).

tff(c_10,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_156,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k5_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_10])).

tff(c_159,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_156])).

tff(c_353,plain,(
    k2_tarski('#skF_4','#skF_3') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_347,c_159])).

tff(c_102,plain,(
    ! [A_66,B_67] : k1_enumset1(A_66,A_66,B_67) = k2_tarski(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_14,plain,(
    ! [E_15,A_9,B_10] : r2_hidden(E_15,k1_enumset1(A_9,B_10,E_15)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_111,plain,(
    ! [B_67,A_66] : r2_hidden(B_67,k2_tarski(A_66,B_67)) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_14])).

tff(c_371,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_353,c_111])).

tff(c_183,plain,(
    ! [E_84,C_85,B_86,A_87] :
      ( E_84 = C_85
      | E_84 = B_86
      | E_84 = A_87
      | ~ r2_hidden(E_84,k1_enumset1(A_87,B_86,C_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_202,plain,(
    ! [E_88,B_89,A_90] :
      ( E_88 = B_89
      | E_88 = A_90
      | E_88 = A_90
      | ~ r2_hidden(E_88,k2_tarski(A_90,B_89)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_183])).

tff(c_211,plain,(
    ! [E_88,A_24] :
      ( E_88 = A_24
      | E_88 = A_24
      | E_88 = A_24
      | ~ r2_hidden(E_88,k1_tarski(A_24)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_202])).

tff(c_382,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_371,c_211])).

tff(c_386,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_52,c_52,c_382])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:45:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.49  
% 2.65/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.49  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.65/1.49  
% 2.65/1.49  %Foreground sorts:
% 2.65/1.49  
% 2.65/1.49  
% 2.65/1.49  %Background operators:
% 2.65/1.49  
% 2.65/1.49  
% 2.65/1.49  %Foreground operators:
% 2.65/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.65/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.65/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.65/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.65/1.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.65/1.49  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.65/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.65/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.65/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.65/1.49  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.65/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.65/1.49  tff('#skF_3', type, '#skF_3': $i).
% 2.65/1.49  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.65/1.49  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.65/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.49  tff('#skF_4', type, '#skF_4': $i).
% 2.65/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.65/1.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.65/1.49  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.65/1.49  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.65/1.49  
% 2.84/1.51  tff(f_73, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 2.84/1.51  tff(f_58, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.84/1.51  tff(f_56, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.84/1.51  tff(f_60, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.84/1.51  tff(f_62, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.84/1.51  tff(f_64, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 2.84/1.51  tff(f_66, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 2.84/1.51  tff(f_68, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 2.84/1.51  tff(f_54, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k1_tarski(H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_enumset1)).
% 2.84/1.51  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.84/1.51  tff(f_35, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.84/1.51  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.84/1.51  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.84/1.51  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.84/1.51  tff(f_52, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.84/1.51  tff(c_52, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.84/1.51  tff(c_40, plain, (![A_25, B_26]: (k1_enumset1(A_25, A_25, B_26)=k2_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.84/1.51  tff(c_38, plain, (![A_24]: (k2_tarski(A_24, A_24)=k1_tarski(A_24))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.84/1.51  tff(c_42, plain, (![A_27, B_28, C_29]: (k2_enumset1(A_27, A_27, B_28, C_29)=k1_enumset1(A_27, B_28, C_29))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.84/1.51  tff(c_44, plain, (![A_30, B_31, C_32, D_33]: (k3_enumset1(A_30, A_30, B_31, C_32, D_33)=k2_enumset1(A_30, B_31, C_32, D_33))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.84/1.51  tff(c_46, plain, (![D_37, A_34, B_35, C_36, E_38]: (k4_enumset1(A_34, A_34, B_35, C_36, D_37, E_38)=k3_enumset1(A_34, B_35, C_36, D_37, E_38))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.84/1.51  tff(c_48, plain, (![E_43, F_44, D_42, A_39, C_41, B_40]: (k5_enumset1(A_39, A_39, B_40, C_41, D_42, E_43, F_44)=k4_enumset1(A_39, B_40, C_41, D_42, E_43, F_44))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.84/1.51  tff(c_50, plain, (![D_48, C_47, A_45, B_46, G_51, E_49, F_50]: (k6_enumset1(A_45, A_45, B_46, C_47, D_48, E_49, F_50, G_51)=k5_enumset1(A_45, B_46, C_47, D_48, E_49, F_50, G_51))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.84/1.51  tff(c_268, plain, (![H_128, G_129, F_127, A_132, D_133, C_134, E_131, B_130]: (k2_xboole_0(k5_enumset1(A_132, B_130, C_134, D_133, E_131, F_127, G_129), k1_tarski(H_128))=k6_enumset1(A_132, B_130, C_134, D_133, E_131, F_127, G_129, H_128))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.84/1.51  tff(c_277, plain, (![H_128, E_43, F_44, D_42, A_39, C_41, B_40]: (k6_enumset1(A_39, A_39, B_40, C_41, D_42, E_43, F_44, H_128)=k2_xboole_0(k4_enumset1(A_39, B_40, C_41, D_42, E_43, F_44), k1_tarski(H_128)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_268])).
% 2.84/1.51  tff(c_281, plain, (![C_137, B_136, E_141, F_140, H_138, D_139, A_135]: (k2_xboole_0(k4_enumset1(A_135, B_136, C_137, D_139, E_141, F_140), k1_tarski(H_138))=k5_enumset1(A_135, B_136, C_137, D_139, E_141, F_140, H_138))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_277])).
% 2.84/1.51  tff(c_290, plain, (![D_37, A_34, B_35, C_36, H_138, E_38]: (k5_enumset1(A_34, A_34, B_35, C_36, D_37, E_38, H_138)=k2_xboole_0(k3_enumset1(A_34, B_35, C_36, D_37, E_38), k1_tarski(H_138)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_281])).
% 2.84/1.51  tff(c_294, plain, (![H_146, C_147, E_144, A_142, D_143, B_145]: (k2_xboole_0(k3_enumset1(A_142, B_145, C_147, D_143, E_144), k1_tarski(H_146))=k4_enumset1(A_142, B_145, C_147, D_143, E_144, H_146))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_290])).
% 2.84/1.51  tff(c_303, plain, (![H_146, D_33, A_30, C_32, B_31]: (k4_enumset1(A_30, A_30, B_31, C_32, D_33, H_146)=k2_xboole_0(k2_enumset1(A_30, B_31, C_32, D_33), k1_tarski(H_146)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_294])).
% 2.84/1.51  tff(c_307, plain, (![C_148, H_150, B_149, D_152, A_151]: (k2_xboole_0(k2_enumset1(A_151, B_149, C_148, D_152), k1_tarski(H_150))=k3_enumset1(A_151, B_149, C_148, D_152, H_150))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_303])).
% 2.84/1.51  tff(c_316, plain, (![A_27, B_28, C_29, H_150]: (k3_enumset1(A_27, A_27, B_28, C_29, H_150)=k2_xboole_0(k1_enumset1(A_27, B_28, C_29), k1_tarski(H_150)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_307])).
% 2.84/1.51  tff(c_321, plain, (![A_157, B_158, C_159, H_160]: (k2_xboole_0(k1_enumset1(A_157, B_158, C_159), k1_tarski(H_160))=k2_enumset1(A_157, B_158, C_159, H_160))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_316])).
% 2.84/1.51  tff(c_330, plain, (![A_25, B_26, H_160]: (k2_xboole_0(k2_tarski(A_25, B_26), k1_tarski(H_160))=k2_enumset1(A_25, A_25, B_26, H_160))), inference(superposition, [status(thm), theory('equality')], [c_40, c_321])).
% 2.84/1.51  tff(c_334, plain, (![A_161, B_162, H_163]: (k2_xboole_0(k2_tarski(A_161, B_162), k1_tarski(H_163))=k1_enumset1(A_161, B_162, H_163))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_330])).
% 2.84/1.51  tff(c_343, plain, (![A_24, H_163]: (k2_xboole_0(k1_tarski(A_24), k1_tarski(H_163))=k1_enumset1(A_24, A_24, H_163))), inference(superposition, [status(thm), theory('equality')], [c_38, c_334])).
% 2.84/1.51  tff(c_347, plain, (![A_164, H_165]: (k2_xboole_0(k1_tarski(A_164), k1_tarski(H_165))=k2_tarski(A_164, H_165))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_343])).
% 2.84/1.51  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.84/1.51  tff(c_8, plain, (![A_6]: (k5_xboole_0(A_6, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.84/1.51  tff(c_54, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.84/1.51  tff(c_93, plain, (![A_64, B_65]: (k3_xboole_0(A_64, B_65)=A_64 | ~r1_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.84/1.51  tff(c_97, plain, (k3_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(resolution, [status(thm)], [c_54, c_93])).
% 2.84/1.51  tff(c_140, plain, (![A_75, B_76]: (k5_xboole_0(A_75, k3_xboole_0(A_75, B_76))=k4_xboole_0(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.84/1.51  tff(c_149, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_97, c_140])).
% 2.84/1.51  tff(c_152, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8, c_149])).
% 2.84/1.51  tff(c_10, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k4_xboole_0(B_8, A_7))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.84/1.51  tff(c_156, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k5_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_152, c_10])).
% 2.84/1.51  tff(c_159, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_156])).
% 2.84/1.51  tff(c_353, plain, (k2_tarski('#skF_4', '#skF_3')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_347, c_159])).
% 2.84/1.51  tff(c_102, plain, (![A_66, B_67]: (k1_enumset1(A_66, A_66, B_67)=k2_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.84/1.51  tff(c_14, plain, (![E_15, A_9, B_10]: (r2_hidden(E_15, k1_enumset1(A_9, B_10, E_15)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.84/1.51  tff(c_111, plain, (![B_67, A_66]: (r2_hidden(B_67, k2_tarski(A_66, B_67)))), inference(superposition, [status(thm), theory('equality')], [c_102, c_14])).
% 2.84/1.51  tff(c_371, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_353, c_111])).
% 2.84/1.51  tff(c_183, plain, (![E_84, C_85, B_86, A_87]: (E_84=C_85 | E_84=B_86 | E_84=A_87 | ~r2_hidden(E_84, k1_enumset1(A_87, B_86, C_85)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.84/1.51  tff(c_202, plain, (![E_88, B_89, A_90]: (E_88=B_89 | E_88=A_90 | E_88=A_90 | ~r2_hidden(E_88, k2_tarski(A_90, B_89)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_183])).
% 2.84/1.51  tff(c_211, plain, (![E_88, A_24]: (E_88=A_24 | E_88=A_24 | E_88=A_24 | ~r2_hidden(E_88, k1_tarski(A_24)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_202])).
% 2.84/1.51  tff(c_382, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_371, c_211])).
% 2.84/1.51  tff(c_386, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_52, c_52, c_382])).
% 2.84/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.84/1.51  
% 2.84/1.51  Inference rules
% 2.84/1.51  ----------------------
% 2.84/1.51  #Ref     : 0
% 2.84/1.51  #Sup     : 78
% 2.84/1.51  #Fact    : 0
% 2.84/1.51  #Define  : 0
% 2.84/1.51  #Split   : 0
% 2.84/1.51  #Chain   : 0
% 2.84/1.51  #Close   : 0
% 2.84/1.51  
% 2.84/1.51  Ordering : KBO
% 2.84/1.51  
% 2.84/1.51  Simplification rules
% 2.84/1.51  ----------------------
% 2.84/1.51  #Subsume      : 0
% 2.84/1.51  #Demod        : 12
% 2.84/1.51  #Tautology    : 55
% 2.84/1.51  #SimpNegUnit  : 1
% 2.84/1.51  #BackRed      : 0
% 2.84/1.51  
% 2.84/1.51  #Partial instantiations: 0
% 2.84/1.51  #Strategies tried      : 1
% 2.84/1.51  
% 2.84/1.51  Timing (in seconds)
% 2.84/1.51  ----------------------
% 2.84/1.51  Preprocessing        : 0.37
% 2.84/1.51  Parsing              : 0.19
% 2.84/1.51  CNF conversion       : 0.03
% 2.84/1.51  Main loop            : 0.26
% 2.84/1.51  Inferencing          : 0.11
% 2.84/1.51  Reduction            : 0.07
% 2.84/1.51  Demodulation         : 0.05
% 2.84/1.51  BG Simplification    : 0.02
% 2.84/1.52  Subsumption          : 0.04
% 2.84/1.52  Abstraction          : 0.02
% 2.84/1.52  MUC search           : 0.00
% 2.84/1.52  Cooper               : 0.00
% 2.84/1.52  Total                : 0.66
% 2.84/1.52  Index Insertion      : 0.00
% 2.84/1.52  Index Deletion       : 0.00
% 2.84/1.52  Index Matching       : 0.00
% 2.84/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
