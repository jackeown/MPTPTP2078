%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:44 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   70 (  93 expanded)
%              Number of leaves         :   33 (  46 expanded)
%              Depth                    :   16
%              Number of atoms          :   63 (  93 expanded)
%              Number of equality atoms :   56 (  85 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_52,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_62,axiom,(
    ! [A,B,C] : k3_enumset1(A,A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_enumset1)).

tff(f_54,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_58,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_60,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_64,axiom,(
    ! [A,B,C,D,E,F] : k6_enumset1(A,A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_enumset1)).

tff(f_50,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k2_tarski(G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).

tff(f_27,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_50,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_36,plain,(
    ! [A_32] : k2_tarski(A_32,A_32) = k1_tarski(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_166,plain,(
    ! [A_87,B_88,C_89,D_90] : k3_enumset1(A_87,A_87,B_88,C_89,D_90) = k2_enumset1(A_87,B_88,C_89,D_90) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_46,plain,(
    ! [A_51,B_52,C_53] : k3_enumset1(A_51,A_51,A_51,B_52,C_53) = k1_enumset1(A_51,B_52,C_53) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_173,plain,(
    ! [B_88,C_89,D_90] : k2_enumset1(B_88,B_88,C_89,D_90) = k1_enumset1(B_88,C_89,D_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_46])).

tff(c_40,plain,(
    ! [A_35,B_36,C_37,D_38] : k3_enumset1(A_35,A_35,B_36,C_37,D_38) = k2_enumset1(A_35,B_36,C_37,D_38) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_38,plain,(
    ! [A_33,B_34] : k1_enumset1(A_33,A_33,B_34) = k2_tarski(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_42,plain,(
    ! [E_43,D_42,A_39,C_41,B_40] : k4_enumset1(A_39,A_39,B_40,C_41,D_42,E_43) = k3_enumset1(A_39,B_40,C_41,D_42,E_43) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_303,plain,(
    ! [C_121,B_122,G_120,F_118,D_119,A_123,E_117] : k6_enumset1(A_123,A_123,B_122,C_121,D_119,E_117,F_118,G_120) = k5_enumset1(A_123,B_122,C_121,D_119,E_117,F_118,G_120) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_48,plain,(
    ! [C_56,E_58,F_59,D_57,B_55,A_54] : k6_enumset1(A_54,A_54,A_54,B_55,C_56,D_57,E_58,F_59) = k4_enumset1(A_54,B_55,C_56,D_57,E_58,F_59) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_310,plain,(
    ! [C_121,B_122,G_120,F_118,D_119,E_117] : k5_enumset1(B_122,B_122,C_121,D_119,E_117,F_118,G_120) = k4_enumset1(B_122,C_121,D_119,E_117,F_118,G_120) ),
    inference(superposition,[status(thm),theory(equality)],[c_303,c_48])).

tff(c_44,plain,(
    ! [C_46,E_48,F_49,G_50,A_44,B_45,D_47] : k6_enumset1(A_44,A_44,B_45,C_46,D_47,E_48,F_49,G_50) = k5_enumset1(A_44,B_45,C_46,D_47,E_48,F_49,G_50) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_348,plain,(
    ! [A_152,B_148,C_147,G_146,D_153,F_151,E_150,H_149] : k2_xboole_0(k4_enumset1(A_152,B_148,C_147,D_153,E_150,F_151),k2_tarski(G_146,H_149)) = k6_enumset1(A_152,B_148,C_147,D_153,E_150,F_151,G_146,H_149) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_357,plain,(
    ! [E_43,G_146,D_42,A_39,H_149,C_41,B_40] : k6_enumset1(A_39,A_39,B_40,C_41,D_42,E_43,G_146,H_149) = k2_xboole_0(k3_enumset1(A_39,B_40,C_41,D_42,E_43),k2_tarski(G_146,H_149)) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_348])).

tff(c_364,plain,(
    ! [B_155,D_157,A_154,H_159,C_156,G_158,E_160] : k2_xboole_0(k3_enumset1(A_154,B_155,C_156,D_157,E_160),k2_tarski(G_158,H_159)) = k5_enumset1(A_154,B_155,C_156,D_157,E_160,G_158,H_159) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_357])).

tff(c_373,plain,(
    ! [A_35,B_36,C_37,H_159,D_38,G_158] : k5_enumset1(A_35,A_35,B_36,C_37,D_38,G_158,H_159) = k2_xboole_0(k2_enumset1(A_35,B_36,C_37,D_38),k2_tarski(G_158,H_159)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_364])).

tff(c_383,plain,(
    ! [B_166,D_165,A_161,C_164,G_163,H_162] : k2_xboole_0(k2_enumset1(A_161,B_166,C_164,D_165),k2_tarski(G_163,H_162)) = k4_enumset1(A_161,B_166,C_164,D_165,G_163,H_162) ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_373])).

tff(c_395,plain,(
    ! [C_89,B_88,G_163,H_162,D_90] : k4_enumset1(B_88,B_88,C_89,D_90,G_163,H_162) = k2_xboole_0(k1_enumset1(B_88,C_89,D_90),k2_tarski(G_163,H_162)) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_383])).

tff(c_408,plain,(
    ! [D_167,H_170,B_171,C_168,G_169] : k2_xboole_0(k1_enumset1(B_171,C_168,D_167),k2_tarski(G_169,H_170)) = k3_enumset1(B_171,C_168,D_167,G_169,H_170) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_395])).

tff(c_417,plain,(
    ! [A_33,B_34,G_169,H_170] : k3_enumset1(A_33,A_33,B_34,G_169,H_170) = k2_xboole_0(k2_tarski(A_33,B_34),k2_tarski(G_169,H_170)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_408])).

tff(c_440,plain,(
    ! [A_181,B_182,G_183,H_184] : k2_xboole_0(k2_tarski(A_181,B_182),k2_tarski(G_183,H_184)) = k2_enumset1(A_181,B_182,G_183,H_184) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_417])).

tff(c_449,plain,(
    ! [A_32,G_183,H_184] : k2_xboole_0(k1_tarski(A_32),k2_tarski(G_183,H_184)) = k2_enumset1(A_32,A_32,G_183,H_184) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_440])).

tff(c_456,plain,(
    ! [A_185,G_186,H_187] : k2_xboole_0(k1_tarski(A_185),k2_tarski(G_186,H_187)) = k1_enumset1(A_185,G_186,H_187) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_449])).

tff(c_468,plain,(
    ! [A_188,A_189] : k2_xboole_0(k1_tarski(A_188),k1_tarski(A_189)) = k1_enumset1(A_188,A_189,A_189) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_456])).

tff(c_2,plain,(
    ! [A_1] : k5_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_52,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_100,plain,(
    ! [A_75,B_76] : k5_xboole_0(A_75,k4_xboole_0(B_76,A_75)) = k2_xboole_0(A_75,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_109,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k5_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_100])).

tff(c_112,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_109])).

tff(c_483,plain,(
    k1_enumset1('#skF_4','#skF_3','#skF_3') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_468,c_112])).

tff(c_8,plain,(
    ! [E_10,A_4,B_5] : r2_hidden(E_10,k1_enumset1(A_4,B_5,E_10)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_525,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_483,c_8])).

tff(c_206,plain,(
    ! [E_94,C_95,B_96,A_97] :
      ( E_94 = C_95
      | E_94 = B_96
      | E_94 = A_97
      | ~ r2_hidden(E_94,k1_enumset1(A_97,B_96,C_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_265,plain,(
    ! [E_101,B_102,A_103] :
      ( E_101 = B_102
      | E_101 = A_103
      | E_101 = A_103
      | ~ r2_hidden(E_101,k2_tarski(A_103,B_102)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_206])).

tff(c_274,plain,(
    ! [E_101,A_32] :
      ( E_101 = A_32
      | E_101 = A_32
      | E_101 = A_32
      | ~ r2_hidden(E_101,k1_tarski(A_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_265])).

tff(c_539,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_525,c_274])).

tff(c_543,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_50,c_50,c_539])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:28:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.53/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.40  
% 2.53/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.40  %$ r2_hidden > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.53/1.40  
% 2.53/1.40  %Foreground sorts:
% 2.53/1.40  
% 2.53/1.40  
% 2.53/1.40  %Background operators:
% 2.53/1.40  
% 2.53/1.40  
% 2.53/1.40  %Foreground operators:
% 2.53/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.53/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.53/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.53/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.53/1.40  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.53/1.40  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.53/1.40  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.53/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.53/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.53/1.40  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.53/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.53/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.53/1.40  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.53/1.40  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.53/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.53/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.53/1.40  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.53/1.40  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.53/1.40  
% 2.53/1.42  tff(f_69, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 2.53/1.42  tff(f_52, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.53/1.42  tff(f_56, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.53/1.42  tff(f_62, axiom, (![A, B, C]: (k3_enumset1(A, A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_enumset1)).
% 2.53/1.42  tff(f_54, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.53/1.42  tff(f_58, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.53/1.42  tff(f_60, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 2.53/1.42  tff(f_64, axiom, (![A, B, C, D, E, F]: (k6_enumset1(A, A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_enumset1)).
% 2.53/1.42  tff(f_50, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k2_tarski(G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_enumset1)).
% 2.53/1.42  tff(f_27, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.53/1.42  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.53/1.42  tff(f_44, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.53/1.42  tff(c_50, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.53/1.42  tff(c_36, plain, (![A_32]: (k2_tarski(A_32, A_32)=k1_tarski(A_32))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.53/1.42  tff(c_166, plain, (![A_87, B_88, C_89, D_90]: (k3_enumset1(A_87, A_87, B_88, C_89, D_90)=k2_enumset1(A_87, B_88, C_89, D_90))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.53/1.42  tff(c_46, plain, (![A_51, B_52, C_53]: (k3_enumset1(A_51, A_51, A_51, B_52, C_53)=k1_enumset1(A_51, B_52, C_53))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.53/1.42  tff(c_173, plain, (![B_88, C_89, D_90]: (k2_enumset1(B_88, B_88, C_89, D_90)=k1_enumset1(B_88, C_89, D_90))), inference(superposition, [status(thm), theory('equality')], [c_166, c_46])).
% 2.53/1.42  tff(c_40, plain, (![A_35, B_36, C_37, D_38]: (k3_enumset1(A_35, A_35, B_36, C_37, D_38)=k2_enumset1(A_35, B_36, C_37, D_38))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.53/1.42  tff(c_38, plain, (![A_33, B_34]: (k1_enumset1(A_33, A_33, B_34)=k2_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.53/1.42  tff(c_42, plain, (![E_43, D_42, A_39, C_41, B_40]: (k4_enumset1(A_39, A_39, B_40, C_41, D_42, E_43)=k3_enumset1(A_39, B_40, C_41, D_42, E_43))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.53/1.42  tff(c_303, plain, (![C_121, B_122, G_120, F_118, D_119, A_123, E_117]: (k6_enumset1(A_123, A_123, B_122, C_121, D_119, E_117, F_118, G_120)=k5_enumset1(A_123, B_122, C_121, D_119, E_117, F_118, G_120))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.53/1.42  tff(c_48, plain, (![C_56, E_58, F_59, D_57, B_55, A_54]: (k6_enumset1(A_54, A_54, A_54, B_55, C_56, D_57, E_58, F_59)=k4_enumset1(A_54, B_55, C_56, D_57, E_58, F_59))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.53/1.42  tff(c_310, plain, (![C_121, B_122, G_120, F_118, D_119, E_117]: (k5_enumset1(B_122, B_122, C_121, D_119, E_117, F_118, G_120)=k4_enumset1(B_122, C_121, D_119, E_117, F_118, G_120))), inference(superposition, [status(thm), theory('equality')], [c_303, c_48])).
% 2.53/1.42  tff(c_44, plain, (![C_46, E_48, F_49, G_50, A_44, B_45, D_47]: (k6_enumset1(A_44, A_44, B_45, C_46, D_47, E_48, F_49, G_50)=k5_enumset1(A_44, B_45, C_46, D_47, E_48, F_49, G_50))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.53/1.42  tff(c_348, plain, (![A_152, B_148, C_147, G_146, D_153, F_151, E_150, H_149]: (k2_xboole_0(k4_enumset1(A_152, B_148, C_147, D_153, E_150, F_151), k2_tarski(G_146, H_149))=k6_enumset1(A_152, B_148, C_147, D_153, E_150, F_151, G_146, H_149))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.53/1.42  tff(c_357, plain, (![E_43, G_146, D_42, A_39, H_149, C_41, B_40]: (k6_enumset1(A_39, A_39, B_40, C_41, D_42, E_43, G_146, H_149)=k2_xboole_0(k3_enumset1(A_39, B_40, C_41, D_42, E_43), k2_tarski(G_146, H_149)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_348])).
% 2.53/1.42  tff(c_364, plain, (![B_155, D_157, A_154, H_159, C_156, G_158, E_160]: (k2_xboole_0(k3_enumset1(A_154, B_155, C_156, D_157, E_160), k2_tarski(G_158, H_159))=k5_enumset1(A_154, B_155, C_156, D_157, E_160, G_158, H_159))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_357])).
% 2.53/1.42  tff(c_373, plain, (![A_35, B_36, C_37, H_159, D_38, G_158]: (k5_enumset1(A_35, A_35, B_36, C_37, D_38, G_158, H_159)=k2_xboole_0(k2_enumset1(A_35, B_36, C_37, D_38), k2_tarski(G_158, H_159)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_364])).
% 2.53/1.42  tff(c_383, plain, (![B_166, D_165, A_161, C_164, G_163, H_162]: (k2_xboole_0(k2_enumset1(A_161, B_166, C_164, D_165), k2_tarski(G_163, H_162))=k4_enumset1(A_161, B_166, C_164, D_165, G_163, H_162))), inference(demodulation, [status(thm), theory('equality')], [c_310, c_373])).
% 2.53/1.42  tff(c_395, plain, (![C_89, B_88, G_163, H_162, D_90]: (k4_enumset1(B_88, B_88, C_89, D_90, G_163, H_162)=k2_xboole_0(k1_enumset1(B_88, C_89, D_90), k2_tarski(G_163, H_162)))), inference(superposition, [status(thm), theory('equality')], [c_173, c_383])).
% 2.53/1.42  tff(c_408, plain, (![D_167, H_170, B_171, C_168, G_169]: (k2_xboole_0(k1_enumset1(B_171, C_168, D_167), k2_tarski(G_169, H_170))=k3_enumset1(B_171, C_168, D_167, G_169, H_170))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_395])).
% 2.53/1.42  tff(c_417, plain, (![A_33, B_34, G_169, H_170]: (k3_enumset1(A_33, A_33, B_34, G_169, H_170)=k2_xboole_0(k2_tarski(A_33, B_34), k2_tarski(G_169, H_170)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_408])).
% 2.53/1.42  tff(c_440, plain, (![A_181, B_182, G_183, H_184]: (k2_xboole_0(k2_tarski(A_181, B_182), k2_tarski(G_183, H_184))=k2_enumset1(A_181, B_182, G_183, H_184))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_417])).
% 2.53/1.42  tff(c_449, plain, (![A_32, G_183, H_184]: (k2_xboole_0(k1_tarski(A_32), k2_tarski(G_183, H_184))=k2_enumset1(A_32, A_32, G_183, H_184))), inference(superposition, [status(thm), theory('equality')], [c_36, c_440])).
% 2.53/1.42  tff(c_456, plain, (![A_185, G_186, H_187]: (k2_xboole_0(k1_tarski(A_185), k2_tarski(G_186, H_187))=k1_enumset1(A_185, G_186, H_187))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_449])).
% 2.53/1.42  tff(c_468, plain, (![A_188, A_189]: (k2_xboole_0(k1_tarski(A_188), k1_tarski(A_189))=k1_enumset1(A_188, A_189, A_189))), inference(superposition, [status(thm), theory('equality')], [c_36, c_456])).
% 2.53/1.42  tff(c_2, plain, (![A_1]: (k5_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.53/1.42  tff(c_52, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.53/1.42  tff(c_100, plain, (![A_75, B_76]: (k5_xboole_0(A_75, k4_xboole_0(B_76, A_75))=k2_xboole_0(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.53/1.42  tff(c_109, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k5_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_52, c_100])).
% 2.53/1.42  tff(c_112, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_109])).
% 2.53/1.42  tff(c_483, plain, (k1_enumset1('#skF_4', '#skF_3', '#skF_3')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_468, c_112])).
% 2.53/1.42  tff(c_8, plain, (![E_10, A_4, B_5]: (r2_hidden(E_10, k1_enumset1(A_4, B_5, E_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.53/1.42  tff(c_525, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_483, c_8])).
% 2.53/1.42  tff(c_206, plain, (![E_94, C_95, B_96, A_97]: (E_94=C_95 | E_94=B_96 | E_94=A_97 | ~r2_hidden(E_94, k1_enumset1(A_97, B_96, C_95)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.53/1.42  tff(c_265, plain, (![E_101, B_102, A_103]: (E_101=B_102 | E_101=A_103 | E_101=A_103 | ~r2_hidden(E_101, k2_tarski(A_103, B_102)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_206])).
% 2.53/1.42  tff(c_274, plain, (![E_101, A_32]: (E_101=A_32 | E_101=A_32 | E_101=A_32 | ~r2_hidden(E_101, k1_tarski(A_32)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_265])).
% 2.53/1.42  tff(c_539, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_525, c_274])).
% 2.53/1.42  tff(c_543, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_50, c_50, c_539])).
% 2.53/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.42  
% 2.53/1.42  Inference rules
% 2.53/1.42  ----------------------
% 2.53/1.42  #Ref     : 0
% 2.53/1.42  #Sup     : 119
% 2.53/1.42  #Fact    : 0
% 2.53/1.42  #Define  : 0
% 2.53/1.42  #Split   : 0
% 2.53/1.42  #Chain   : 0
% 2.53/1.42  #Close   : 0
% 2.53/1.42  
% 2.53/1.42  Ordering : KBO
% 2.53/1.42  
% 2.53/1.42  Simplification rules
% 2.53/1.42  ----------------------
% 2.53/1.42  #Subsume      : 0
% 2.53/1.42  #Demod        : 22
% 2.53/1.42  #Tautology    : 76
% 2.53/1.42  #SimpNegUnit  : 1
% 2.53/1.42  #BackRed      : 0
% 2.53/1.42  
% 2.53/1.42  #Partial instantiations: 0
% 2.53/1.42  #Strategies tried      : 1
% 2.53/1.42  
% 2.53/1.42  Timing (in seconds)
% 2.53/1.42  ----------------------
% 2.53/1.42  Preprocessing        : 0.34
% 2.53/1.42  Parsing              : 0.18
% 2.53/1.42  CNF conversion       : 0.02
% 2.53/1.42  Main loop            : 0.27
% 2.53/1.42  Inferencing          : 0.11
% 2.53/1.42  Reduction            : 0.08
% 2.53/1.42  Demodulation         : 0.06
% 2.53/1.42  BG Simplification    : 0.02
% 2.53/1.42  Subsumption          : 0.04
% 2.53/1.42  Abstraction          : 0.02
% 2.53/1.42  MUC search           : 0.00
% 2.53/1.42  Cooper               : 0.00
% 2.53/1.42  Total                : 0.63
% 2.53/1.42  Index Insertion      : 0.00
% 2.53/1.42  Index Deletion       : 0.00
% 2.53/1.42  Index Matching       : 0.00
% 2.53/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
