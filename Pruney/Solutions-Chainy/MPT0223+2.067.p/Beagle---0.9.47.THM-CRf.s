%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:25 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :   75 (  96 expanded)
%              Number of leaves         :   35 (  47 expanded)
%              Depth                    :   17
%              Number of atoms          :   68 (  96 expanded)
%              Number of equality atoms :   60 (  87 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

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

tff(f_29,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_48,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_54,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_42,plain,(
    ! [A_35,B_36] : k1_enumset1(A_35,A_35,B_36) = k2_tarski(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_40,plain,(
    ! [A_34] : k2_tarski(A_34,A_34) = k1_tarski(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_44,plain,(
    ! [A_37,B_38,C_39] : k2_enumset1(A_37,A_37,B_38,C_39) = k1_enumset1(A_37,B_38,C_39) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_46,plain,(
    ! [A_40,B_41,C_42,D_43] : k3_enumset1(A_40,A_40,B_41,C_42,D_43) = k2_enumset1(A_40,B_41,C_42,D_43) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_48,plain,(
    ! [C_46,E_48,A_44,B_45,D_47] : k4_enumset1(A_44,A_44,B_45,C_46,D_47,E_48) = k3_enumset1(A_44,B_45,C_46,D_47,E_48) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_50,plain,(
    ! [D_52,C_51,F_54,B_50,A_49,E_53] : k5_enumset1(A_49,A_49,B_50,C_51,D_52,E_53,F_54) = k4_enumset1(A_49,B_50,C_51,D_52,E_53,F_54) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_52,plain,(
    ! [B_56,E_59,G_61,C_57,A_55,F_60,D_58] : k6_enumset1(A_55,A_55,B_56,C_57,D_58,E_59,F_60,G_61) = k5_enumset1(A_55,B_56,C_57,D_58,E_59,F_60,G_61) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_448,plain,(
    ! [B_148,H_150,C_152,A_149,G_154,D_147,E_153,F_151] : k2_xboole_0(k5_enumset1(A_149,B_148,C_152,D_147,E_153,F_151,G_154),k1_tarski(H_150)) = k6_enumset1(A_149,B_148,C_152,D_147,E_153,F_151,G_154,H_150) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_457,plain,(
    ! [D_52,C_51,H_150,F_54,B_50,A_49,E_53] : k6_enumset1(A_49,A_49,B_50,C_51,D_52,E_53,F_54,H_150) = k2_xboole_0(k4_enumset1(A_49,B_50,C_51,D_52,E_53,F_54),k1_tarski(H_150)) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_448])).

tff(c_473,plain,(
    ! [A_167,C_163,D_168,F_166,H_169,E_164,B_165] : k2_xboole_0(k4_enumset1(A_167,B_165,C_163,D_168,E_164,F_166),k1_tarski(H_169)) = k5_enumset1(A_167,B_165,C_163,D_168,E_164,F_166,H_169) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_457])).

tff(c_482,plain,(
    ! [C_46,E_48,H_169,A_44,B_45,D_47] : k5_enumset1(A_44,A_44,B_45,C_46,D_47,E_48,H_169) = k2_xboole_0(k3_enumset1(A_44,B_45,C_46,D_47,E_48),k1_tarski(H_169)) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_473])).

tff(c_486,plain,(
    ! [H_171,D_172,B_174,E_170,C_173,A_175] : k2_xboole_0(k3_enumset1(A_175,B_174,C_173,D_172,E_170),k1_tarski(H_171)) = k4_enumset1(A_175,B_174,C_173,D_172,E_170,H_171) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_482])).

tff(c_495,plain,(
    ! [C_42,H_171,A_40,D_43,B_41] : k4_enumset1(A_40,A_40,B_41,C_42,D_43,H_171) = k2_xboole_0(k2_enumset1(A_40,B_41,C_42,D_43),k1_tarski(H_171)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_486])).

tff(c_499,plain,(
    ! [B_180,A_176,D_178,H_177,C_179] : k2_xboole_0(k2_enumset1(A_176,B_180,C_179,D_178),k1_tarski(H_177)) = k3_enumset1(A_176,B_180,C_179,D_178,H_177) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_495])).

tff(c_517,plain,(
    ! [A_37,B_38,C_39,H_177] : k3_enumset1(A_37,A_37,B_38,C_39,H_177) = k2_xboole_0(k1_enumset1(A_37,B_38,C_39),k1_tarski(H_177)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_499])).

tff(c_521,plain,(
    ! [A_181,B_182,C_183,H_184] : k2_xboole_0(k1_enumset1(A_181,B_182,C_183),k1_tarski(H_184)) = k2_enumset1(A_181,B_182,C_183,H_184) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_517])).

tff(c_536,plain,(
    ! [A_35,B_36,H_184] : k2_xboole_0(k2_tarski(A_35,B_36),k1_tarski(H_184)) = k2_enumset1(A_35,A_35,B_36,H_184) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_521])).

tff(c_540,plain,(
    ! [A_185,B_186,H_187] : k2_xboole_0(k2_tarski(A_185,B_186),k1_tarski(H_187)) = k1_enumset1(A_185,B_186,H_187) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_536])).

tff(c_549,plain,(
    ! [A_34,H_187] : k2_xboole_0(k1_tarski(A_34),k1_tarski(H_187)) = k1_enumset1(A_34,A_34,H_187) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_540])).

tff(c_554,plain,(
    ! [A_192,H_193] : k2_xboole_0(k1_tarski(A_192),k1_tarski(H_193)) = k2_tarski(A_192,H_193) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_549])).

tff(c_4,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_4] : k5_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_128,plain,(
    ! [A_81,B_82] : k5_xboole_0(A_81,k3_xboole_0(A_81,B_82)) = k4_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_137,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_128])).

tff(c_140,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_137])).

tff(c_145,plain,(
    ! [A_83,B_84] : k5_xboole_0(A_83,k4_xboole_0(B_84,A_83)) = k2_xboole_0(A_83,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_154,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k5_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_145])).

tff(c_157,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_154])).

tff(c_560,plain,(
    k2_tarski('#skF_4','#skF_3') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_554,c_157])).

tff(c_95,plain,(
    ! [A_74,B_75] : k1_enumset1(A_74,A_74,B_75) = k2_tarski(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_12,plain,(
    ! [E_13,A_7,B_8] : r2_hidden(E_13,k1_enumset1(A_7,B_8,E_13)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_101,plain,(
    ! [B_75,A_74] : r2_hidden(B_75,k2_tarski(A_74,B_75)) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_12])).

tff(c_581,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_560,c_101])).

tff(c_321,plain,(
    ! [E_101,C_102,B_103,A_104] :
      ( E_101 = C_102
      | E_101 = B_103
      | E_101 = A_104
      | ~ r2_hidden(E_101,k1_enumset1(A_104,B_103,C_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_347,plain,(
    ! [E_105,B_106,A_107] :
      ( E_105 = B_106
      | E_105 = A_107
      | E_105 = A_107
      | ~ r2_hidden(E_105,k2_tarski(A_107,B_106)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_321])).

tff(c_356,plain,(
    ! [E_105,A_34] :
      ( E_105 = A_34
      | E_105 = A_34
      | E_105 = A_34
      | ~ r2_hidden(E_105,k1_tarski(A_34)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_347])).

tff(c_589,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_581,c_356])).

tff(c_593,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_54,c_54,c_589])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:49:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.43  
% 2.61/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.43  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.61/1.43  
% 2.61/1.43  %Foreground sorts:
% 2.61/1.43  
% 2.61/1.43  
% 2.61/1.43  %Background operators:
% 2.61/1.43  
% 2.61/1.43  
% 2.61/1.43  %Foreground operators:
% 2.61/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.61/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.61/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.61/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.61/1.43  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.61/1.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.61/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.61/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.61/1.43  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.61/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.61/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.61/1.43  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.61/1.43  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.61/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.61/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.61/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.61/1.43  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.61/1.43  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.61/1.43  
% 2.87/1.45  tff(f_73, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 2.87/1.45  tff(f_58, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.87/1.45  tff(f_56, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.87/1.45  tff(f_60, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.87/1.45  tff(f_62, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.87/1.45  tff(f_64, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 2.87/1.45  tff(f_66, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 2.87/1.45  tff(f_68, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 2.87/1.45  tff(f_54, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k1_tarski(H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_enumset1)).
% 2.87/1.45  tff(f_29, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.87/1.45  tff(f_31, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.87/1.45  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.87/1.45  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.87/1.45  tff(f_48, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.87/1.45  tff(c_54, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.87/1.45  tff(c_42, plain, (![A_35, B_36]: (k1_enumset1(A_35, A_35, B_36)=k2_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.87/1.45  tff(c_40, plain, (![A_34]: (k2_tarski(A_34, A_34)=k1_tarski(A_34))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.87/1.45  tff(c_44, plain, (![A_37, B_38, C_39]: (k2_enumset1(A_37, A_37, B_38, C_39)=k1_enumset1(A_37, B_38, C_39))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.87/1.45  tff(c_46, plain, (![A_40, B_41, C_42, D_43]: (k3_enumset1(A_40, A_40, B_41, C_42, D_43)=k2_enumset1(A_40, B_41, C_42, D_43))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.87/1.45  tff(c_48, plain, (![C_46, E_48, A_44, B_45, D_47]: (k4_enumset1(A_44, A_44, B_45, C_46, D_47, E_48)=k3_enumset1(A_44, B_45, C_46, D_47, E_48))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.87/1.45  tff(c_50, plain, (![D_52, C_51, F_54, B_50, A_49, E_53]: (k5_enumset1(A_49, A_49, B_50, C_51, D_52, E_53, F_54)=k4_enumset1(A_49, B_50, C_51, D_52, E_53, F_54))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.87/1.45  tff(c_52, plain, (![B_56, E_59, G_61, C_57, A_55, F_60, D_58]: (k6_enumset1(A_55, A_55, B_56, C_57, D_58, E_59, F_60, G_61)=k5_enumset1(A_55, B_56, C_57, D_58, E_59, F_60, G_61))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.87/1.45  tff(c_448, plain, (![B_148, H_150, C_152, A_149, G_154, D_147, E_153, F_151]: (k2_xboole_0(k5_enumset1(A_149, B_148, C_152, D_147, E_153, F_151, G_154), k1_tarski(H_150))=k6_enumset1(A_149, B_148, C_152, D_147, E_153, F_151, G_154, H_150))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.87/1.45  tff(c_457, plain, (![D_52, C_51, H_150, F_54, B_50, A_49, E_53]: (k6_enumset1(A_49, A_49, B_50, C_51, D_52, E_53, F_54, H_150)=k2_xboole_0(k4_enumset1(A_49, B_50, C_51, D_52, E_53, F_54), k1_tarski(H_150)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_448])).
% 2.87/1.45  tff(c_473, plain, (![A_167, C_163, D_168, F_166, H_169, E_164, B_165]: (k2_xboole_0(k4_enumset1(A_167, B_165, C_163, D_168, E_164, F_166), k1_tarski(H_169))=k5_enumset1(A_167, B_165, C_163, D_168, E_164, F_166, H_169))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_457])).
% 2.87/1.45  tff(c_482, plain, (![C_46, E_48, H_169, A_44, B_45, D_47]: (k5_enumset1(A_44, A_44, B_45, C_46, D_47, E_48, H_169)=k2_xboole_0(k3_enumset1(A_44, B_45, C_46, D_47, E_48), k1_tarski(H_169)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_473])).
% 2.87/1.45  tff(c_486, plain, (![H_171, D_172, B_174, E_170, C_173, A_175]: (k2_xboole_0(k3_enumset1(A_175, B_174, C_173, D_172, E_170), k1_tarski(H_171))=k4_enumset1(A_175, B_174, C_173, D_172, E_170, H_171))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_482])).
% 2.87/1.45  tff(c_495, plain, (![C_42, H_171, A_40, D_43, B_41]: (k4_enumset1(A_40, A_40, B_41, C_42, D_43, H_171)=k2_xboole_0(k2_enumset1(A_40, B_41, C_42, D_43), k1_tarski(H_171)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_486])).
% 2.87/1.45  tff(c_499, plain, (![B_180, A_176, D_178, H_177, C_179]: (k2_xboole_0(k2_enumset1(A_176, B_180, C_179, D_178), k1_tarski(H_177))=k3_enumset1(A_176, B_180, C_179, D_178, H_177))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_495])).
% 2.87/1.45  tff(c_517, plain, (![A_37, B_38, C_39, H_177]: (k3_enumset1(A_37, A_37, B_38, C_39, H_177)=k2_xboole_0(k1_enumset1(A_37, B_38, C_39), k1_tarski(H_177)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_499])).
% 2.87/1.45  tff(c_521, plain, (![A_181, B_182, C_183, H_184]: (k2_xboole_0(k1_enumset1(A_181, B_182, C_183), k1_tarski(H_184))=k2_enumset1(A_181, B_182, C_183, H_184))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_517])).
% 2.87/1.45  tff(c_536, plain, (![A_35, B_36, H_184]: (k2_xboole_0(k2_tarski(A_35, B_36), k1_tarski(H_184))=k2_enumset1(A_35, A_35, B_36, H_184))), inference(superposition, [status(thm), theory('equality')], [c_42, c_521])).
% 2.87/1.45  tff(c_540, plain, (![A_185, B_186, H_187]: (k2_xboole_0(k2_tarski(A_185, B_186), k1_tarski(H_187))=k1_enumset1(A_185, B_186, H_187))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_536])).
% 2.87/1.45  tff(c_549, plain, (![A_34, H_187]: (k2_xboole_0(k1_tarski(A_34), k1_tarski(H_187))=k1_enumset1(A_34, A_34, H_187))), inference(superposition, [status(thm), theory('equality')], [c_40, c_540])).
% 2.87/1.45  tff(c_554, plain, (![A_192, H_193]: (k2_xboole_0(k1_tarski(A_192), k1_tarski(H_193))=k2_tarski(A_192, H_193))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_549])).
% 2.87/1.45  tff(c_4, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.87/1.45  tff(c_6, plain, (![A_4]: (k5_xboole_0(A_4, A_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.87/1.45  tff(c_56, plain, (k3_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.87/1.45  tff(c_128, plain, (![A_81, B_82]: (k5_xboole_0(A_81, k3_xboole_0(A_81, B_82))=k4_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.87/1.45  tff(c_137, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_128])).
% 2.87/1.45  tff(c_140, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6, c_137])).
% 2.87/1.45  tff(c_145, plain, (![A_83, B_84]: (k5_xboole_0(A_83, k4_xboole_0(B_84, A_83))=k2_xboole_0(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.87/1.45  tff(c_154, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k5_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_140, c_145])).
% 2.87/1.45  tff(c_157, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_154])).
% 2.87/1.45  tff(c_560, plain, (k2_tarski('#skF_4', '#skF_3')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_554, c_157])).
% 2.87/1.45  tff(c_95, plain, (![A_74, B_75]: (k1_enumset1(A_74, A_74, B_75)=k2_tarski(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.87/1.45  tff(c_12, plain, (![E_13, A_7, B_8]: (r2_hidden(E_13, k1_enumset1(A_7, B_8, E_13)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.87/1.45  tff(c_101, plain, (![B_75, A_74]: (r2_hidden(B_75, k2_tarski(A_74, B_75)))), inference(superposition, [status(thm), theory('equality')], [c_95, c_12])).
% 2.87/1.45  tff(c_581, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_560, c_101])).
% 2.87/1.45  tff(c_321, plain, (![E_101, C_102, B_103, A_104]: (E_101=C_102 | E_101=B_103 | E_101=A_104 | ~r2_hidden(E_101, k1_enumset1(A_104, B_103, C_102)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.87/1.45  tff(c_347, plain, (![E_105, B_106, A_107]: (E_105=B_106 | E_105=A_107 | E_105=A_107 | ~r2_hidden(E_105, k2_tarski(A_107, B_106)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_321])).
% 2.87/1.45  tff(c_356, plain, (![E_105, A_34]: (E_105=A_34 | E_105=A_34 | E_105=A_34 | ~r2_hidden(E_105, k1_tarski(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_347])).
% 2.87/1.45  tff(c_589, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_581, c_356])).
% 2.87/1.45  tff(c_593, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_54, c_54, c_589])).
% 2.87/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.45  
% 2.87/1.45  Inference rules
% 2.87/1.45  ----------------------
% 2.87/1.45  #Ref     : 0
% 2.87/1.45  #Sup     : 128
% 2.87/1.45  #Fact    : 0
% 2.87/1.45  #Define  : 0
% 2.87/1.45  #Split   : 0
% 2.87/1.45  #Chain   : 0
% 2.87/1.45  #Close   : 0
% 2.87/1.45  
% 2.87/1.45  Ordering : KBO
% 2.87/1.45  
% 2.87/1.45  Simplification rules
% 2.87/1.45  ----------------------
% 2.87/1.45  #Subsume      : 5
% 2.87/1.45  #Demod        : 26
% 2.87/1.45  #Tautology    : 91
% 2.87/1.45  #SimpNegUnit  : 1
% 2.87/1.45  #BackRed      : 0
% 2.87/1.45  
% 2.87/1.45  #Partial instantiations: 0
% 2.87/1.45  #Strategies tried      : 1
% 2.87/1.45  
% 2.87/1.45  Timing (in seconds)
% 2.87/1.45  ----------------------
% 2.87/1.45  Preprocessing        : 0.31
% 2.87/1.45  Parsing              : 0.16
% 2.87/1.45  CNF conversion       : 0.02
% 2.87/1.45  Main loop            : 0.30
% 2.87/1.45  Inferencing          : 0.12
% 2.87/1.45  Reduction            : 0.09
% 2.87/1.45  Demodulation         : 0.07
% 2.87/1.45  BG Simplification    : 0.02
% 2.87/1.45  Subsumption          : 0.05
% 2.87/1.45  Abstraction          : 0.02
% 2.87/1.45  MUC search           : 0.00
% 2.87/1.45  Cooper               : 0.00
% 2.87/1.45  Total                : 0.65
% 2.87/1.45  Index Insertion      : 0.00
% 2.87/1.45  Index Deletion       : 0.00
% 2.87/1.45  Index Matching       : 0.00
% 2.87/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
