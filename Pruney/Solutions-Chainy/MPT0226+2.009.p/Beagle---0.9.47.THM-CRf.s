%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:39 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :   69 (  90 expanded)
%              Number of leaves         :   33 (  45 expanded)
%              Depth                    :   17
%              Number of atoms          :   62 (  90 expanded)
%              Number of equality atoms :   54 (  81 expanded)
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

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_58,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_62,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_64,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_66,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_68,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_70,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k1_tarski(H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_56,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_44,plain,(
    ! [A_28,B_29] : k1_enumset1(A_28,A_28,B_29) = k2_tarski(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_42,plain,(
    ! [A_27] : k2_tarski(A_27,A_27) = k1_tarski(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_46,plain,(
    ! [A_30,B_31,C_32] : k2_enumset1(A_30,A_30,B_31,C_32) = k1_enumset1(A_30,B_31,C_32) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_48,plain,(
    ! [A_33,B_34,C_35,D_36] : k3_enumset1(A_33,A_33,B_34,C_35,D_36) = k2_enumset1(A_33,B_34,C_35,D_36) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_50,plain,(
    ! [C_39,B_38,A_37,D_40,E_41] : k4_enumset1(A_37,A_37,B_38,C_39,D_40,E_41) = k3_enumset1(A_37,B_38,C_39,D_40,E_41) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_52,plain,(
    ! [B_43,A_42,D_45,E_46,C_44,F_47] : k5_enumset1(A_42,A_42,B_43,C_44,D_45,E_46,F_47) = k4_enumset1(A_42,B_43,C_44,D_45,E_46,F_47) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_54,plain,(
    ! [B_49,F_53,A_48,G_54,D_51,E_52,C_50] : k6_enumset1(A_48,A_48,B_49,C_50,D_51,E_52,F_53,G_54) = k5_enumset1(A_48,B_49,C_50,D_51,E_52,F_53,G_54) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_929,plain,(
    ! [C_158,B_161,E_159,D_165,H_160,A_162,G_163,F_164] : k2_xboole_0(k5_enumset1(A_162,B_161,C_158,D_165,E_159,F_164,G_163),k1_tarski(H_160)) = k6_enumset1(A_162,B_161,C_158,D_165,E_159,F_164,G_163,H_160) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_938,plain,(
    ! [B_43,A_42,D_45,E_46,H_160,C_44,F_47] : k6_enumset1(A_42,A_42,B_43,C_44,D_45,E_46,F_47,H_160) = k2_xboole_0(k4_enumset1(A_42,B_43,C_44,D_45,E_46,F_47),k1_tarski(H_160)) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_929])).

tff(c_943,plain,(
    ! [C_176,B_172,D_171,E_170,H_174,A_173,F_175] : k2_xboole_0(k4_enumset1(A_173,B_172,C_176,D_171,E_170,F_175),k1_tarski(H_174)) = k5_enumset1(A_173,B_172,C_176,D_171,E_170,F_175,H_174) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_938])).

tff(c_952,plain,(
    ! [C_39,B_38,A_37,D_40,E_41,H_174] : k5_enumset1(A_37,A_37,B_38,C_39,D_40,E_41,H_174) = k2_xboole_0(k3_enumset1(A_37,B_38,C_39,D_40,E_41),k1_tarski(H_174)) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_943])).

tff(c_956,plain,(
    ! [H_182,D_179,B_178,C_181,A_177,E_180] : k2_xboole_0(k3_enumset1(A_177,B_178,C_181,D_179,E_180),k1_tarski(H_182)) = k4_enumset1(A_177,B_178,C_181,D_179,E_180,H_182) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_952])).

tff(c_965,plain,(
    ! [D_36,H_182,A_33,B_34,C_35] : k4_enumset1(A_33,A_33,B_34,C_35,D_36,H_182) = k2_xboole_0(k2_enumset1(A_33,B_34,C_35,D_36),k1_tarski(H_182)) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_956])).

tff(c_969,plain,(
    ! [H_186,C_184,A_183,D_185,B_187] : k2_xboole_0(k2_enumset1(A_183,B_187,C_184,D_185),k1_tarski(H_186)) = k3_enumset1(A_183,B_187,C_184,D_185,H_186) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_965])).

tff(c_978,plain,(
    ! [A_30,B_31,C_32,H_186] : k3_enumset1(A_30,A_30,B_31,C_32,H_186) = k2_xboole_0(k1_enumset1(A_30,B_31,C_32),k1_tarski(H_186)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_969])).

tff(c_983,plain,(
    ! [A_192,B_193,C_194,H_195] : k2_xboole_0(k1_enumset1(A_192,B_193,C_194),k1_tarski(H_195)) = k2_enumset1(A_192,B_193,C_194,H_195) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_978])).

tff(c_992,plain,(
    ! [A_28,B_29,H_195] : k2_xboole_0(k2_tarski(A_28,B_29),k1_tarski(H_195)) = k2_enumset1(A_28,A_28,B_29,H_195) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_983])).

tff(c_996,plain,(
    ! [A_196,B_197,H_198] : k2_xboole_0(k2_tarski(A_196,B_197),k1_tarski(H_198)) = k1_enumset1(A_196,B_197,H_198) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_992])).

tff(c_1011,plain,(
    ! [A_27,H_198] : k2_xboole_0(k1_tarski(A_27),k1_tarski(H_198)) = k1_enumset1(A_27,A_27,H_198) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_996])).

tff(c_1015,plain,(
    ! [A_199,H_200] : k2_xboole_0(k1_tarski(A_199),k1_tarski(H_200)) = k2_tarski(A_199,H_200) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1011])).

tff(c_8,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_58,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_184,plain,(
    ! [A_77,B_78] : k5_xboole_0(A_77,k4_xboole_0(B_78,A_77)) = k2_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_193,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k5_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_184])).

tff(c_196,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_193])).

tff(c_1025,plain,(
    k2_tarski('#skF_4','#skF_3') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1015,c_196])).

tff(c_141,plain,(
    ! [A_70,B_71] : k1_enumset1(A_70,A_70,B_71) = k2_tarski(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_18,plain,(
    ! [E_18,A_12,B_13] : r2_hidden(E_18,k1_enumset1(A_12,B_13,E_18)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_153,plain,(
    ! [B_71,A_70] : r2_hidden(B_71,k2_tarski(A_70,B_71)) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_18])).

tff(c_1052,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1025,c_153])).

tff(c_436,plain,(
    ! [E_98,C_99,B_100,A_101] :
      ( E_98 = C_99
      | E_98 = B_100
      | E_98 = A_101
      | ~ r2_hidden(E_98,k1_enumset1(A_101,B_100,C_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_455,plain,(
    ! [E_102,B_103,A_104] :
      ( E_102 = B_103
      | E_102 = A_104
      | E_102 = A_104
      | ~ r2_hidden(E_102,k2_tarski(A_104,B_103)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_436])).

tff(c_470,plain,(
    ! [E_102,A_27] :
      ( E_102 = A_27
      | E_102 = A_27
      | E_102 = A_27
      | ~ r2_hidden(E_102,k1_tarski(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_455])).

tff(c_1063,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1052,c_470])).

tff(c_1067,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_56,c_56,c_1063])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:24:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.98/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.46  
% 2.98/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.46  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.98/1.46  
% 2.98/1.46  %Foreground sorts:
% 2.98/1.46  
% 2.98/1.46  
% 2.98/1.46  %Background operators:
% 2.98/1.46  
% 2.98/1.46  
% 2.98/1.46  %Foreground operators:
% 2.98/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.98/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.98/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.98/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.98/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.98/1.46  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.98/1.46  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.98/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.98/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.98/1.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.98/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.98/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.98/1.46  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.98/1.46  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.98/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.98/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.98/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.98/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.98/1.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.98/1.46  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.98/1.46  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.98/1.46  
% 2.98/1.47  tff(f_75, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 2.98/1.47  tff(f_60, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.98/1.47  tff(f_58, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.98/1.47  tff(f_62, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.98/1.47  tff(f_64, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.98/1.47  tff(f_66, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.98/1.47  tff(f_68, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 2.98/1.47  tff(f_70, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 2.98/1.47  tff(f_56, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k1_tarski(H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_enumset1)).
% 2.98/1.47  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.98/1.47  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.98/1.47  tff(f_54, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.98/1.47  tff(c_56, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.98/1.47  tff(c_44, plain, (![A_28, B_29]: (k1_enumset1(A_28, A_28, B_29)=k2_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.98/1.47  tff(c_42, plain, (![A_27]: (k2_tarski(A_27, A_27)=k1_tarski(A_27))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.98/1.47  tff(c_46, plain, (![A_30, B_31, C_32]: (k2_enumset1(A_30, A_30, B_31, C_32)=k1_enumset1(A_30, B_31, C_32))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.98/1.47  tff(c_48, plain, (![A_33, B_34, C_35, D_36]: (k3_enumset1(A_33, A_33, B_34, C_35, D_36)=k2_enumset1(A_33, B_34, C_35, D_36))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.98/1.47  tff(c_50, plain, (![C_39, B_38, A_37, D_40, E_41]: (k4_enumset1(A_37, A_37, B_38, C_39, D_40, E_41)=k3_enumset1(A_37, B_38, C_39, D_40, E_41))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.98/1.47  tff(c_52, plain, (![B_43, A_42, D_45, E_46, C_44, F_47]: (k5_enumset1(A_42, A_42, B_43, C_44, D_45, E_46, F_47)=k4_enumset1(A_42, B_43, C_44, D_45, E_46, F_47))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.98/1.47  tff(c_54, plain, (![B_49, F_53, A_48, G_54, D_51, E_52, C_50]: (k6_enumset1(A_48, A_48, B_49, C_50, D_51, E_52, F_53, G_54)=k5_enumset1(A_48, B_49, C_50, D_51, E_52, F_53, G_54))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.98/1.47  tff(c_929, plain, (![C_158, B_161, E_159, D_165, H_160, A_162, G_163, F_164]: (k2_xboole_0(k5_enumset1(A_162, B_161, C_158, D_165, E_159, F_164, G_163), k1_tarski(H_160))=k6_enumset1(A_162, B_161, C_158, D_165, E_159, F_164, G_163, H_160))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.98/1.47  tff(c_938, plain, (![B_43, A_42, D_45, E_46, H_160, C_44, F_47]: (k6_enumset1(A_42, A_42, B_43, C_44, D_45, E_46, F_47, H_160)=k2_xboole_0(k4_enumset1(A_42, B_43, C_44, D_45, E_46, F_47), k1_tarski(H_160)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_929])).
% 2.98/1.47  tff(c_943, plain, (![C_176, B_172, D_171, E_170, H_174, A_173, F_175]: (k2_xboole_0(k4_enumset1(A_173, B_172, C_176, D_171, E_170, F_175), k1_tarski(H_174))=k5_enumset1(A_173, B_172, C_176, D_171, E_170, F_175, H_174))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_938])).
% 2.98/1.47  tff(c_952, plain, (![C_39, B_38, A_37, D_40, E_41, H_174]: (k5_enumset1(A_37, A_37, B_38, C_39, D_40, E_41, H_174)=k2_xboole_0(k3_enumset1(A_37, B_38, C_39, D_40, E_41), k1_tarski(H_174)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_943])).
% 2.98/1.47  tff(c_956, plain, (![H_182, D_179, B_178, C_181, A_177, E_180]: (k2_xboole_0(k3_enumset1(A_177, B_178, C_181, D_179, E_180), k1_tarski(H_182))=k4_enumset1(A_177, B_178, C_181, D_179, E_180, H_182))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_952])).
% 2.98/1.47  tff(c_965, plain, (![D_36, H_182, A_33, B_34, C_35]: (k4_enumset1(A_33, A_33, B_34, C_35, D_36, H_182)=k2_xboole_0(k2_enumset1(A_33, B_34, C_35, D_36), k1_tarski(H_182)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_956])).
% 2.98/1.47  tff(c_969, plain, (![H_186, C_184, A_183, D_185, B_187]: (k2_xboole_0(k2_enumset1(A_183, B_187, C_184, D_185), k1_tarski(H_186))=k3_enumset1(A_183, B_187, C_184, D_185, H_186))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_965])).
% 2.98/1.47  tff(c_978, plain, (![A_30, B_31, C_32, H_186]: (k3_enumset1(A_30, A_30, B_31, C_32, H_186)=k2_xboole_0(k1_enumset1(A_30, B_31, C_32), k1_tarski(H_186)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_969])).
% 2.98/1.47  tff(c_983, plain, (![A_192, B_193, C_194, H_195]: (k2_xboole_0(k1_enumset1(A_192, B_193, C_194), k1_tarski(H_195))=k2_enumset1(A_192, B_193, C_194, H_195))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_978])).
% 2.98/1.47  tff(c_992, plain, (![A_28, B_29, H_195]: (k2_xboole_0(k2_tarski(A_28, B_29), k1_tarski(H_195))=k2_enumset1(A_28, A_28, B_29, H_195))), inference(superposition, [status(thm), theory('equality')], [c_44, c_983])).
% 2.98/1.47  tff(c_996, plain, (![A_196, B_197, H_198]: (k2_xboole_0(k2_tarski(A_196, B_197), k1_tarski(H_198))=k1_enumset1(A_196, B_197, H_198))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_992])).
% 2.98/1.47  tff(c_1011, plain, (![A_27, H_198]: (k2_xboole_0(k1_tarski(A_27), k1_tarski(H_198))=k1_enumset1(A_27, A_27, H_198))), inference(superposition, [status(thm), theory('equality')], [c_42, c_996])).
% 2.98/1.47  tff(c_1015, plain, (![A_199, H_200]: (k2_xboole_0(k1_tarski(A_199), k1_tarski(H_200))=k2_tarski(A_199, H_200))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1011])).
% 2.98/1.47  tff(c_8, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.98/1.47  tff(c_58, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.98/1.47  tff(c_184, plain, (![A_77, B_78]: (k5_xboole_0(A_77, k4_xboole_0(B_78, A_77))=k2_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.98/1.47  tff(c_193, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k5_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_58, c_184])).
% 2.98/1.47  tff(c_196, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_193])).
% 2.98/1.47  tff(c_1025, plain, (k2_tarski('#skF_4', '#skF_3')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1015, c_196])).
% 2.98/1.47  tff(c_141, plain, (![A_70, B_71]: (k1_enumset1(A_70, A_70, B_71)=k2_tarski(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.98/1.47  tff(c_18, plain, (![E_18, A_12, B_13]: (r2_hidden(E_18, k1_enumset1(A_12, B_13, E_18)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.98/1.47  tff(c_153, plain, (![B_71, A_70]: (r2_hidden(B_71, k2_tarski(A_70, B_71)))), inference(superposition, [status(thm), theory('equality')], [c_141, c_18])).
% 2.98/1.47  tff(c_1052, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1025, c_153])).
% 2.98/1.47  tff(c_436, plain, (![E_98, C_99, B_100, A_101]: (E_98=C_99 | E_98=B_100 | E_98=A_101 | ~r2_hidden(E_98, k1_enumset1(A_101, B_100, C_99)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.98/1.47  tff(c_455, plain, (![E_102, B_103, A_104]: (E_102=B_103 | E_102=A_104 | E_102=A_104 | ~r2_hidden(E_102, k2_tarski(A_104, B_103)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_436])).
% 2.98/1.47  tff(c_470, plain, (![E_102, A_27]: (E_102=A_27 | E_102=A_27 | E_102=A_27 | ~r2_hidden(E_102, k1_tarski(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_455])).
% 2.98/1.47  tff(c_1063, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_1052, c_470])).
% 2.98/1.47  tff(c_1067, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_56, c_56, c_1063])).
% 2.98/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.47  
% 2.98/1.47  Inference rules
% 2.98/1.47  ----------------------
% 2.98/1.47  #Ref     : 0
% 2.98/1.47  #Sup     : 247
% 2.98/1.47  #Fact    : 0
% 2.98/1.47  #Define  : 0
% 2.98/1.47  #Split   : 0
% 2.98/1.47  #Chain   : 0
% 2.98/1.47  #Close   : 0
% 2.98/1.47  
% 2.98/1.47  Ordering : KBO
% 2.98/1.47  
% 2.98/1.47  Simplification rules
% 2.98/1.47  ----------------------
% 2.98/1.47  #Subsume      : 4
% 2.98/1.47  #Demod        : 247
% 2.98/1.47  #Tautology    : 174
% 2.98/1.47  #SimpNegUnit  : 1
% 2.98/1.47  #BackRed      : 0
% 2.98/1.47  
% 2.98/1.47  #Partial instantiations: 0
% 2.98/1.47  #Strategies tried      : 1
% 2.98/1.47  
% 2.98/1.47  Timing (in seconds)
% 2.98/1.47  ----------------------
% 2.98/1.48  Preprocessing        : 0.32
% 2.98/1.48  Parsing              : 0.16
% 2.98/1.48  CNF conversion       : 0.02
% 2.98/1.48  Main loop            : 0.39
% 2.98/1.48  Inferencing          : 0.14
% 2.98/1.48  Reduction            : 0.14
% 2.98/1.48  Demodulation         : 0.11
% 2.98/1.48  BG Simplification    : 0.02
% 2.98/1.48  Subsumption          : 0.06
% 2.98/1.48  Abstraction          : 0.02
% 2.98/1.48  MUC search           : 0.00
% 2.98/1.48  Cooper               : 0.00
% 2.98/1.48  Total                : 0.74
% 2.98/1.48  Index Insertion      : 0.00
% 2.98/1.48  Index Deletion       : 0.00
% 2.98/1.48  Index Matching       : 0.00
% 2.98/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
