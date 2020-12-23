%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:43 EST 2020

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :   70 (  91 expanded)
%              Number of leaves         :   34 (  46 expanded)
%              Depth                    :   17
%              Number of atoms          :   62 (  90 expanded)
%              Number of equality atoms :   54 (  81 expanded)
%              Maximal formula depth    :   12 (   5 average)
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

tff(f_79,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_62,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_66,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_68,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_70,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_72,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_74,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_60,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k1_tarski(H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_58,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_46,plain,(
    ! [A_31,B_32] : k1_enumset1(A_31,A_31,B_32) = k2_tarski(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_44,plain,(
    ! [A_30] : k2_tarski(A_30,A_30) = k1_tarski(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_48,plain,(
    ! [A_33,B_34,C_35] : k2_enumset1(A_33,A_33,B_34,C_35) = k1_enumset1(A_33,B_34,C_35) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_50,plain,(
    ! [A_36,B_37,C_38,D_39] : k3_enumset1(A_36,A_36,B_37,C_38,D_39) = k2_enumset1(A_36,B_37,C_38,D_39) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_52,plain,(
    ! [E_44,C_42,A_40,D_43,B_41] : k4_enumset1(A_40,A_40,B_41,C_42,D_43,E_44) = k3_enumset1(A_40,B_41,C_42,D_43,E_44) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_54,plain,(
    ! [D_48,C_47,A_45,B_46,E_49,F_50] : k5_enumset1(A_45,A_45,B_46,C_47,D_48,E_49,F_50) = k4_enumset1(A_45,B_46,C_47,D_48,E_49,F_50) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_56,plain,(
    ! [G_57,B_52,E_55,F_56,C_53,D_54,A_51] : k6_enumset1(A_51,A_51,B_52,C_53,D_54,E_55,F_56,G_57) = k5_enumset1(A_51,B_52,C_53,D_54,E_55,F_56,G_57) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_468,plain,(
    ! [D_157,C_152,F_154,G_155,E_153,H_156,B_158,A_151] : k2_xboole_0(k5_enumset1(A_151,B_158,C_152,D_157,E_153,F_154,G_155),k1_tarski(H_156)) = k6_enumset1(A_151,B_158,C_152,D_157,E_153,F_154,G_155,H_156) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_477,plain,(
    ! [D_48,C_47,A_45,B_46,H_156,E_49,F_50] : k6_enumset1(A_45,A_45,B_46,C_47,D_48,E_49,F_50,H_156) = k2_xboole_0(k4_enumset1(A_45,B_46,C_47,D_48,E_49,F_50),k1_tarski(H_156)) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_468])).

tff(c_481,plain,(
    ! [D_162,C_163,H_159,E_164,A_161,F_165,B_160] : k2_xboole_0(k4_enumset1(A_161,B_160,C_163,D_162,E_164,F_165),k1_tarski(H_159)) = k5_enumset1(A_161,B_160,C_163,D_162,E_164,F_165,H_159) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_477])).

tff(c_490,plain,(
    ! [E_44,C_42,H_159,A_40,D_43,B_41] : k5_enumset1(A_40,A_40,B_41,C_42,D_43,E_44,H_159) = k2_xboole_0(k3_enumset1(A_40,B_41,C_42,D_43,E_44),k1_tarski(H_159)) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_481])).

tff(c_494,plain,(
    ! [E_166,A_167,C_170,D_168,H_169,B_171] : k2_xboole_0(k3_enumset1(A_167,B_171,C_170,D_168,E_166),k1_tarski(H_169)) = k4_enumset1(A_167,B_171,C_170,D_168,E_166,H_169) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_490])).

tff(c_503,plain,(
    ! [D_39,A_36,H_169,C_38,B_37] : k4_enumset1(A_36,A_36,B_37,C_38,D_39,H_169) = k2_xboole_0(k2_enumset1(A_36,B_37,C_38,D_39),k1_tarski(H_169)) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_494])).

tff(c_508,plain,(
    ! [H_176,A_177,C_180,B_179,D_178] : k2_xboole_0(k2_enumset1(A_177,B_179,C_180,D_178),k1_tarski(H_176)) = k3_enumset1(A_177,B_179,C_180,D_178,H_176) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_503])).

tff(c_526,plain,(
    ! [A_33,B_34,C_35,H_176] : k3_enumset1(A_33,A_33,B_34,C_35,H_176) = k2_xboole_0(k1_enumset1(A_33,B_34,C_35),k1_tarski(H_176)) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_508])).

tff(c_530,plain,(
    ! [A_181,B_182,C_183,H_184] : k2_xboole_0(k1_enumset1(A_181,B_182,C_183),k1_tarski(H_184)) = k2_enumset1(A_181,B_182,C_183,H_184) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_526])).

tff(c_545,plain,(
    ! [A_31,B_32,H_184] : k2_xboole_0(k2_tarski(A_31,B_32),k1_tarski(H_184)) = k2_enumset1(A_31,A_31,B_32,H_184) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_530])).

tff(c_549,plain,(
    ! [A_185,B_186,H_187] : k2_xboole_0(k2_tarski(A_185,B_186),k1_tarski(H_187)) = k1_enumset1(A_185,B_186,H_187) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_545])).

tff(c_558,plain,(
    ! [A_30,H_187] : k2_xboole_0(k1_tarski(A_30),k1_tarski(H_187)) = k1_enumset1(A_30,A_30,H_187) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_549])).

tff(c_563,plain,(
    ! [A_192,H_193] : k2_xboole_0(k1_tarski(A_192),k1_tarski(H_193)) = k2_tarski(A_192,H_193) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_558])).

tff(c_10,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_60,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_152,plain,(
    ! [A_85,B_86] : k5_xboole_0(A_85,k4_xboole_0(B_86,A_85)) = k2_xboole_0(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_161,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k5_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_152])).

tff(c_164,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_161])).

tff(c_569,plain,(
    k2_tarski('#skF_4','#skF_3') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_563,c_164])).

tff(c_103,plain,(
    ! [A_70,B_71] : k1_enumset1(A_70,A_70,B_71) = k2_tarski(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_18,plain,(
    ! [E_17,A_11,B_12] : r2_hidden(E_17,k1_enumset1(A_11,B_12,E_17)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_112,plain,(
    ! [B_71,A_70] : r2_hidden(B_71,k2_tarski(A_70,B_71)) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_18])).

tff(c_587,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_569,c_112])).

tff(c_341,plain,(
    ! [E_105,C_106,B_107,A_108] :
      ( E_105 = C_106
      | E_105 = B_107
      | E_105 = A_108
      | ~ r2_hidden(E_105,k1_enumset1(A_108,B_107,C_106)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_367,plain,(
    ! [E_109,B_110,A_111] :
      ( E_109 = B_110
      | E_109 = A_111
      | E_109 = A_111
      | ~ r2_hidden(E_109,k2_tarski(A_111,B_110)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_341])).

tff(c_376,plain,(
    ! [E_109,A_30] :
      ( E_109 = A_30
      | E_109 = A_30
      | E_109 = A_30
      | ~ r2_hidden(E_109,k1_tarski(A_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_367])).

tff(c_598,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_587,c_376])).

tff(c_602,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_58,c_58,c_598])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:04:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.64/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.37  
% 2.64/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.37  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.64/1.37  
% 2.64/1.37  %Foreground sorts:
% 2.64/1.37  
% 2.64/1.37  
% 2.64/1.37  %Background operators:
% 2.64/1.37  
% 2.64/1.37  
% 2.64/1.37  %Foreground operators:
% 2.64/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.64/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.64/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.64/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.64/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.64/1.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.64/1.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.64/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.64/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.64/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.64/1.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.64/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.64/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.64/1.37  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.64/1.37  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.64/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.64/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.64/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.64/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.64/1.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.64/1.37  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.64/1.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.64/1.37  
% 2.64/1.39  tff(f_79, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 2.64/1.39  tff(f_64, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.64/1.39  tff(f_62, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.64/1.39  tff(f_66, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.64/1.39  tff(f_68, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.64/1.39  tff(f_70, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.64/1.39  tff(f_72, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 2.64/1.39  tff(f_74, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 2.64/1.39  tff(f_60, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k1_tarski(H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_enumset1)).
% 2.64/1.39  tff(f_37, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.64/1.39  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.64/1.39  tff(f_56, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.64/1.39  tff(c_58, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.64/1.39  tff(c_46, plain, (![A_31, B_32]: (k1_enumset1(A_31, A_31, B_32)=k2_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.64/1.39  tff(c_44, plain, (![A_30]: (k2_tarski(A_30, A_30)=k1_tarski(A_30))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.64/1.39  tff(c_48, plain, (![A_33, B_34, C_35]: (k2_enumset1(A_33, A_33, B_34, C_35)=k1_enumset1(A_33, B_34, C_35))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.64/1.39  tff(c_50, plain, (![A_36, B_37, C_38, D_39]: (k3_enumset1(A_36, A_36, B_37, C_38, D_39)=k2_enumset1(A_36, B_37, C_38, D_39))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.64/1.39  tff(c_52, plain, (![E_44, C_42, A_40, D_43, B_41]: (k4_enumset1(A_40, A_40, B_41, C_42, D_43, E_44)=k3_enumset1(A_40, B_41, C_42, D_43, E_44))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.64/1.39  tff(c_54, plain, (![D_48, C_47, A_45, B_46, E_49, F_50]: (k5_enumset1(A_45, A_45, B_46, C_47, D_48, E_49, F_50)=k4_enumset1(A_45, B_46, C_47, D_48, E_49, F_50))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.64/1.39  tff(c_56, plain, (![G_57, B_52, E_55, F_56, C_53, D_54, A_51]: (k6_enumset1(A_51, A_51, B_52, C_53, D_54, E_55, F_56, G_57)=k5_enumset1(A_51, B_52, C_53, D_54, E_55, F_56, G_57))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.64/1.39  tff(c_468, plain, (![D_157, C_152, F_154, G_155, E_153, H_156, B_158, A_151]: (k2_xboole_0(k5_enumset1(A_151, B_158, C_152, D_157, E_153, F_154, G_155), k1_tarski(H_156))=k6_enumset1(A_151, B_158, C_152, D_157, E_153, F_154, G_155, H_156))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.64/1.39  tff(c_477, plain, (![D_48, C_47, A_45, B_46, H_156, E_49, F_50]: (k6_enumset1(A_45, A_45, B_46, C_47, D_48, E_49, F_50, H_156)=k2_xboole_0(k4_enumset1(A_45, B_46, C_47, D_48, E_49, F_50), k1_tarski(H_156)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_468])).
% 2.64/1.39  tff(c_481, plain, (![D_162, C_163, H_159, E_164, A_161, F_165, B_160]: (k2_xboole_0(k4_enumset1(A_161, B_160, C_163, D_162, E_164, F_165), k1_tarski(H_159))=k5_enumset1(A_161, B_160, C_163, D_162, E_164, F_165, H_159))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_477])).
% 2.64/1.39  tff(c_490, plain, (![E_44, C_42, H_159, A_40, D_43, B_41]: (k5_enumset1(A_40, A_40, B_41, C_42, D_43, E_44, H_159)=k2_xboole_0(k3_enumset1(A_40, B_41, C_42, D_43, E_44), k1_tarski(H_159)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_481])).
% 2.64/1.39  tff(c_494, plain, (![E_166, A_167, C_170, D_168, H_169, B_171]: (k2_xboole_0(k3_enumset1(A_167, B_171, C_170, D_168, E_166), k1_tarski(H_169))=k4_enumset1(A_167, B_171, C_170, D_168, E_166, H_169))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_490])).
% 2.64/1.39  tff(c_503, plain, (![D_39, A_36, H_169, C_38, B_37]: (k4_enumset1(A_36, A_36, B_37, C_38, D_39, H_169)=k2_xboole_0(k2_enumset1(A_36, B_37, C_38, D_39), k1_tarski(H_169)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_494])).
% 2.64/1.39  tff(c_508, plain, (![H_176, A_177, C_180, B_179, D_178]: (k2_xboole_0(k2_enumset1(A_177, B_179, C_180, D_178), k1_tarski(H_176))=k3_enumset1(A_177, B_179, C_180, D_178, H_176))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_503])).
% 2.64/1.39  tff(c_526, plain, (![A_33, B_34, C_35, H_176]: (k3_enumset1(A_33, A_33, B_34, C_35, H_176)=k2_xboole_0(k1_enumset1(A_33, B_34, C_35), k1_tarski(H_176)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_508])).
% 2.64/1.39  tff(c_530, plain, (![A_181, B_182, C_183, H_184]: (k2_xboole_0(k1_enumset1(A_181, B_182, C_183), k1_tarski(H_184))=k2_enumset1(A_181, B_182, C_183, H_184))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_526])).
% 2.64/1.39  tff(c_545, plain, (![A_31, B_32, H_184]: (k2_xboole_0(k2_tarski(A_31, B_32), k1_tarski(H_184))=k2_enumset1(A_31, A_31, B_32, H_184))), inference(superposition, [status(thm), theory('equality')], [c_46, c_530])).
% 2.64/1.39  tff(c_549, plain, (![A_185, B_186, H_187]: (k2_xboole_0(k2_tarski(A_185, B_186), k1_tarski(H_187))=k1_enumset1(A_185, B_186, H_187))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_545])).
% 2.64/1.39  tff(c_558, plain, (![A_30, H_187]: (k2_xboole_0(k1_tarski(A_30), k1_tarski(H_187))=k1_enumset1(A_30, A_30, H_187))), inference(superposition, [status(thm), theory('equality')], [c_44, c_549])).
% 2.64/1.39  tff(c_563, plain, (![A_192, H_193]: (k2_xboole_0(k1_tarski(A_192), k1_tarski(H_193))=k2_tarski(A_192, H_193))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_558])).
% 2.64/1.39  tff(c_10, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.64/1.39  tff(c_60, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.64/1.39  tff(c_152, plain, (![A_85, B_86]: (k5_xboole_0(A_85, k4_xboole_0(B_86, A_85))=k2_xboole_0(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.64/1.39  tff(c_161, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k5_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_60, c_152])).
% 2.64/1.39  tff(c_164, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_161])).
% 2.64/1.39  tff(c_569, plain, (k2_tarski('#skF_4', '#skF_3')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_563, c_164])).
% 2.64/1.39  tff(c_103, plain, (![A_70, B_71]: (k1_enumset1(A_70, A_70, B_71)=k2_tarski(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.64/1.39  tff(c_18, plain, (![E_17, A_11, B_12]: (r2_hidden(E_17, k1_enumset1(A_11, B_12, E_17)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.64/1.39  tff(c_112, plain, (![B_71, A_70]: (r2_hidden(B_71, k2_tarski(A_70, B_71)))), inference(superposition, [status(thm), theory('equality')], [c_103, c_18])).
% 2.64/1.39  tff(c_587, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_569, c_112])).
% 2.64/1.39  tff(c_341, plain, (![E_105, C_106, B_107, A_108]: (E_105=C_106 | E_105=B_107 | E_105=A_108 | ~r2_hidden(E_105, k1_enumset1(A_108, B_107, C_106)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.64/1.39  tff(c_367, plain, (![E_109, B_110, A_111]: (E_109=B_110 | E_109=A_111 | E_109=A_111 | ~r2_hidden(E_109, k2_tarski(A_111, B_110)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_341])).
% 2.64/1.39  tff(c_376, plain, (![E_109, A_30]: (E_109=A_30 | E_109=A_30 | E_109=A_30 | ~r2_hidden(E_109, k1_tarski(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_367])).
% 2.64/1.39  tff(c_598, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_587, c_376])).
% 2.64/1.39  tff(c_602, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_58, c_58, c_598])).
% 2.64/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.39  
% 2.64/1.39  Inference rules
% 2.64/1.39  ----------------------
% 2.64/1.39  #Ref     : 0
% 2.64/1.39  #Sup     : 128
% 2.64/1.39  #Fact    : 0
% 2.64/1.39  #Define  : 0
% 2.64/1.39  #Split   : 0
% 2.64/1.39  #Chain   : 0
% 2.64/1.39  #Close   : 0
% 2.64/1.39  
% 2.64/1.39  Ordering : KBO
% 2.64/1.39  
% 2.64/1.39  Simplification rules
% 2.64/1.39  ----------------------
% 2.64/1.39  #Subsume      : 5
% 2.64/1.39  #Demod        : 27
% 2.64/1.39  #Tautology    : 91
% 2.64/1.39  #SimpNegUnit  : 1
% 2.64/1.39  #BackRed      : 0
% 2.64/1.39  
% 2.64/1.39  #Partial instantiations: 0
% 2.64/1.39  #Strategies tried      : 1
% 2.64/1.39  
% 2.64/1.39  Timing (in seconds)
% 2.64/1.39  ----------------------
% 2.64/1.39  Preprocessing        : 0.33
% 2.64/1.39  Parsing              : 0.17
% 2.64/1.39  CNF conversion       : 0.02
% 2.64/1.39  Main loop            : 0.29
% 2.64/1.39  Inferencing          : 0.11
% 2.64/1.39  Reduction            : 0.09
% 2.64/1.39  Demodulation         : 0.07
% 2.64/1.39  BG Simplification    : 0.02
% 2.64/1.39  Subsumption          : 0.05
% 2.64/1.39  Abstraction          : 0.02
% 2.64/1.39  MUC search           : 0.00
% 2.64/1.39  Cooper               : 0.00
% 2.64/1.39  Total                : 0.66
% 2.64/1.39  Index Insertion      : 0.00
% 2.64/1.39  Index Deletion       : 0.00
% 2.64/1.39  Index Matching       : 0.00
% 2.64/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
