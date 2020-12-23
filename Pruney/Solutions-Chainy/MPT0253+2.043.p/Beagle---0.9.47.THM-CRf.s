%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:19 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :   72 (  84 expanded)
%              Number of leaves         :   37 (  44 expanded)
%              Depth                    :   15
%              Number of atoms          :   65 (  81 expanded)
%              Number of equality atoms :   44 (  56 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,B) )
       => k2_xboole_0(k2_tarski(A,C),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(C,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_enumset1)).

tff(f_45,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_39,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_tarski(F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).

tff(f_57,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_44,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_42,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_292,plain,(
    ! [A_99,B_100,C_101] :
      ( r1_tarski(k2_tarski(A_99,B_100),C_101)
      | ~ r2_hidden(B_100,C_101)
      | ~ r2_hidden(A_99,C_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_379,plain,(
    ! [A_121,B_122,C_123] :
      ( k4_xboole_0(k2_tarski(A_121,B_122),C_123) = k1_xboole_0
      | ~ r2_hidden(B_122,C_123)
      | ~ r2_hidden(A_121,C_123) ) ),
    inference(resolution,[status(thm)],[c_292,c_4])).

tff(c_10,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = k2_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_391,plain,(
    ! [C_123,A_121,B_122] :
      ( k2_xboole_0(C_123,k2_tarski(A_121,B_122)) = k2_xboole_0(C_123,k1_xboole_0)
      | ~ r2_hidden(B_122,C_123)
      | ~ r2_hidden(A_121,C_123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_379,c_10])).

tff(c_401,plain,(
    ! [C_123,A_121,B_122] :
      ( k2_xboole_0(C_123,k2_tarski(A_121,B_122)) = C_123
      | ~ r2_hidden(B_122,C_123)
      | ~ r2_hidden(A_121,C_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_391])).

tff(c_169,plain,(
    ! [C_76,B_77,A_78] : k1_enumset1(C_76,B_77,A_78) = k1_enumset1(A_78,B_77,C_76) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    ! [A_21,B_22] : k1_enumset1(A_21,A_21,B_22) = k2_tarski(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_185,plain,(
    ! [C_76,B_77] : k1_enumset1(C_76,B_77,B_77) = k2_tarski(B_77,C_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_20])).

tff(c_14,plain,(
    ! [A_11,B_12] : k2_xboole_0(k1_tarski(A_11),k1_tarski(B_12)) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_20] : k2_tarski(A_20,A_20) = k1_tarski(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    ! [A_26,B_27,C_28,D_29] : k3_enumset1(A_26,A_26,B_27,C_28,D_29) = k2_enumset1(A_26,B_27,C_28,D_29) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    ! [D_33,A_30,C_32,B_31,E_34] : k4_enumset1(A_30,A_30,B_31,C_32,D_33,E_34) = k3_enumset1(A_30,B_31,C_32,D_33,E_34) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    ! [A_23,B_24,C_25] : k2_enumset1(A_23,A_23,B_24,C_25) = k1_enumset1(A_23,B_24,C_25) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_28,plain,(
    ! [A_35,F_40,B_36,C_37,D_38,E_39] : k5_enumset1(A_35,A_35,B_36,C_37,D_38,E_39,F_40) = k4_enumset1(A_35,B_36,C_37,D_38,E_39,F_40) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_432,plain,(
    ! [C_140,F_134,A_138,B_136,E_137,G_139,D_135] : k2_xboole_0(k3_enumset1(A_138,B_136,C_140,D_135,E_137),k2_tarski(F_134,G_139)) = k5_enumset1(A_138,B_136,C_140,D_135,E_137,F_134,G_139) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_448,plain,(
    ! [B_27,D_29,F_134,A_26,G_139,C_28] : k5_enumset1(A_26,A_26,B_27,C_28,D_29,F_134,G_139) = k2_xboole_0(k2_enumset1(A_26,B_27,C_28,D_29),k2_tarski(F_134,G_139)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_432])).

tff(c_455,plain,(
    ! [F_146,D_141,G_144,A_143,B_142,C_145] : k2_xboole_0(k2_enumset1(A_143,B_142,C_145,D_141),k2_tarski(F_146,G_144)) = k4_enumset1(A_143,B_142,C_145,D_141,F_146,G_144) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_448])).

tff(c_471,plain,(
    ! [F_146,G_144,A_23,B_24,C_25] : k4_enumset1(A_23,A_23,B_24,C_25,F_146,G_144) = k2_xboole_0(k1_enumset1(A_23,B_24,C_25),k2_tarski(F_146,G_144)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_455])).

tff(c_478,plain,(
    ! [B_150,C_147,G_149,F_148,A_151] : k2_xboole_0(k1_enumset1(A_151,B_150,C_147),k2_tarski(F_148,G_149)) = k3_enumset1(A_151,B_150,C_147,F_148,G_149) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_471])).

tff(c_503,plain,(
    ! [A_21,B_22,F_148,G_149] : k3_enumset1(A_21,A_21,B_22,F_148,G_149) = k2_xboole_0(k2_tarski(A_21,B_22),k2_tarski(F_148,G_149)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_478])).

tff(c_510,plain,(
    ! [A_152,B_153,F_154,G_155] : k2_xboole_0(k2_tarski(A_152,B_153),k2_tarski(F_154,G_155)) = k2_enumset1(A_152,B_153,F_154,G_155) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_503])).

tff(c_671,plain,(
    ! [A_166,B_167,A_168] : k2_xboole_0(k2_tarski(A_166,B_167),k1_tarski(A_168)) = k2_enumset1(A_166,B_167,A_168,A_168) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_510])).

tff(c_695,plain,(
    ! [B_167,A_168] : k2_xboole_0(k2_tarski(B_167,B_167),k1_tarski(A_168)) = k1_enumset1(B_167,A_168,A_168) ),
    inference(superposition,[status(thm),theory(equality)],[c_671,c_22])).

tff(c_731,plain,(
    ! [B_169,A_170] : k2_tarski(B_169,A_170) = k2_tarski(A_170,B_169) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_14,c_18,c_695])).

tff(c_32,plain,(
    ! [A_48,B_49] : k3_tarski(k2_tarski(A_48,B_49)) = k2_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_854,plain,(
    ! [B_171,A_172] : k3_tarski(k2_tarski(B_171,A_172)) = k2_xboole_0(A_172,B_171) ),
    inference(superposition,[status(thm),theory(equality)],[c_731,c_32])).

tff(c_860,plain,(
    ! [B_171,A_172] : k2_xboole_0(B_171,A_172) = k2_xboole_0(A_172,B_171) ),
    inference(superposition,[status(thm),theory(equality)],[c_854,c_32])).

tff(c_40,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_3'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_880,plain,(
    k2_xboole_0('#skF_2',k2_tarski('#skF_1','#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_860,c_40])).

tff(c_1167,plain,
    ( ~ r2_hidden('#skF_3','#skF_2')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_401,c_880])).

tff(c_1171,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_1167])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:08:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.19/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.53  
% 3.19/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.54  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.19/1.54  
% 3.19/1.54  %Foreground sorts:
% 3.19/1.54  
% 3.19/1.54  
% 3.19/1.54  %Background operators:
% 3.19/1.54  
% 3.19/1.54  
% 3.19/1.54  %Foreground operators:
% 3.19/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.19/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.19/1.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.19/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.19/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.19/1.54  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.19/1.54  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.19/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.19/1.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.19/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.19/1.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.19/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.19/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.19/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.19/1.54  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.19/1.54  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.19/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.19/1.54  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.19/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.19/1.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.19/1.54  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.19/1.54  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.19/1.54  
% 3.19/1.55  tff(f_70, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k2_xboole_0(k2_tarski(A, C), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_zfmisc_1)).
% 3.19/1.55  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.19/1.55  tff(f_63, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.19/1.55  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.19/1.55  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.19/1.55  tff(f_37, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(C, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_enumset1)).
% 3.19/1.55  tff(f_45, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.19/1.55  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 3.19/1.55  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.19/1.55  tff(f_49, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 3.19/1.55  tff(f_51, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 3.19/1.55  tff(f_47, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.19/1.55  tff(f_53, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 3.19/1.55  tff(f_41, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_tarski(F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_enumset1)).
% 3.19/1.55  tff(f_57, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.19/1.55  tff(c_44, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.19/1.55  tff(c_42, plain, (r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.19/1.55  tff(c_8, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.19/1.55  tff(c_292, plain, (![A_99, B_100, C_101]: (r1_tarski(k2_tarski(A_99, B_100), C_101) | ~r2_hidden(B_100, C_101) | ~r2_hidden(A_99, C_101))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.19/1.55  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.19/1.55  tff(c_379, plain, (![A_121, B_122, C_123]: (k4_xboole_0(k2_tarski(A_121, B_122), C_123)=k1_xboole_0 | ~r2_hidden(B_122, C_123) | ~r2_hidden(A_121, C_123))), inference(resolution, [status(thm)], [c_292, c_4])).
% 3.19/1.55  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(B_7, A_6))=k2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.19/1.55  tff(c_391, plain, (![C_123, A_121, B_122]: (k2_xboole_0(C_123, k2_tarski(A_121, B_122))=k2_xboole_0(C_123, k1_xboole_0) | ~r2_hidden(B_122, C_123) | ~r2_hidden(A_121, C_123))), inference(superposition, [status(thm), theory('equality')], [c_379, c_10])).
% 3.19/1.55  tff(c_401, plain, (![C_123, A_121, B_122]: (k2_xboole_0(C_123, k2_tarski(A_121, B_122))=C_123 | ~r2_hidden(B_122, C_123) | ~r2_hidden(A_121, C_123))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_391])).
% 3.19/1.55  tff(c_169, plain, (![C_76, B_77, A_78]: (k1_enumset1(C_76, B_77, A_78)=k1_enumset1(A_78, B_77, C_76))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.19/1.55  tff(c_20, plain, (![A_21, B_22]: (k1_enumset1(A_21, A_21, B_22)=k2_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.19/1.55  tff(c_185, plain, (![C_76, B_77]: (k1_enumset1(C_76, B_77, B_77)=k2_tarski(B_77, C_76))), inference(superposition, [status(thm), theory('equality')], [c_169, c_20])).
% 3.19/1.55  tff(c_14, plain, (![A_11, B_12]: (k2_xboole_0(k1_tarski(A_11), k1_tarski(B_12))=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.19/1.55  tff(c_18, plain, (![A_20]: (k2_tarski(A_20, A_20)=k1_tarski(A_20))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.19/1.55  tff(c_24, plain, (![A_26, B_27, C_28, D_29]: (k3_enumset1(A_26, A_26, B_27, C_28, D_29)=k2_enumset1(A_26, B_27, C_28, D_29))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.19/1.55  tff(c_26, plain, (![D_33, A_30, C_32, B_31, E_34]: (k4_enumset1(A_30, A_30, B_31, C_32, D_33, E_34)=k3_enumset1(A_30, B_31, C_32, D_33, E_34))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.19/1.55  tff(c_22, plain, (![A_23, B_24, C_25]: (k2_enumset1(A_23, A_23, B_24, C_25)=k1_enumset1(A_23, B_24, C_25))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.19/1.55  tff(c_28, plain, (![A_35, F_40, B_36, C_37, D_38, E_39]: (k5_enumset1(A_35, A_35, B_36, C_37, D_38, E_39, F_40)=k4_enumset1(A_35, B_36, C_37, D_38, E_39, F_40))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.19/1.55  tff(c_432, plain, (![C_140, F_134, A_138, B_136, E_137, G_139, D_135]: (k2_xboole_0(k3_enumset1(A_138, B_136, C_140, D_135, E_137), k2_tarski(F_134, G_139))=k5_enumset1(A_138, B_136, C_140, D_135, E_137, F_134, G_139))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.19/1.55  tff(c_448, plain, (![B_27, D_29, F_134, A_26, G_139, C_28]: (k5_enumset1(A_26, A_26, B_27, C_28, D_29, F_134, G_139)=k2_xboole_0(k2_enumset1(A_26, B_27, C_28, D_29), k2_tarski(F_134, G_139)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_432])).
% 3.19/1.55  tff(c_455, plain, (![F_146, D_141, G_144, A_143, B_142, C_145]: (k2_xboole_0(k2_enumset1(A_143, B_142, C_145, D_141), k2_tarski(F_146, G_144))=k4_enumset1(A_143, B_142, C_145, D_141, F_146, G_144))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_448])).
% 3.19/1.55  tff(c_471, plain, (![F_146, G_144, A_23, B_24, C_25]: (k4_enumset1(A_23, A_23, B_24, C_25, F_146, G_144)=k2_xboole_0(k1_enumset1(A_23, B_24, C_25), k2_tarski(F_146, G_144)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_455])).
% 3.19/1.55  tff(c_478, plain, (![B_150, C_147, G_149, F_148, A_151]: (k2_xboole_0(k1_enumset1(A_151, B_150, C_147), k2_tarski(F_148, G_149))=k3_enumset1(A_151, B_150, C_147, F_148, G_149))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_471])).
% 3.19/1.55  tff(c_503, plain, (![A_21, B_22, F_148, G_149]: (k3_enumset1(A_21, A_21, B_22, F_148, G_149)=k2_xboole_0(k2_tarski(A_21, B_22), k2_tarski(F_148, G_149)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_478])).
% 3.19/1.55  tff(c_510, plain, (![A_152, B_153, F_154, G_155]: (k2_xboole_0(k2_tarski(A_152, B_153), k2_tarski(F_154, G_155))=k2_enumset1(A_152, B_153, F_154, G_155))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_503])).
% 3.19/1.55  tff(c_671, plain, (![A_166, B_167, A_168]: (k2_xboole_0(k2_tarski(A_166, B_167), k1_tarski(A_168))=k2_enumset1(A_166, B_167, A_168, A_168))), inference(superposition, [status(thm), theory('equality')], [c_18, c_510])).
% 3.19/1.55  tff(c_695, plain, (![B_167, A_168]: (k2_xboole_0(k2_tarski(B_167, B_167), k1_tarski(A_168))=k1_enumset1(B_167, A_168, A_168))), inference(superposition, [status(thm), theory('equality')], [c_671, c_22])).
% 3.19/1.55  tff(c_731, plain, (![B_169, A_170]: (k2_tarski(B_169, A_170)=k2_tarski(A_170, B_169))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_14, c_18, c_695])).
% 3.19/1.55  tff(c_32, plain, (![A_48, B_49]: (k3_tarski(k2_tarski(A_48, B_49))=k2_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.19/1.55  tff(c_854, plain, (![B_171, A_172]: (k3_tarski(k2_tarski(B_171, A_172))=k2_xboole_0(A_172, B_171))), inference(superposition, [status(thm), theory('equality')], [c_731, c_32])).
% 3.19/1.55  tff(c_860, plain, (![B_171, A_172]: (k2_xboole_0(B_171, A_172)=k2_xboole_0(A_172, B_171))), inference(superposition, [status(thm), theory('equality')], [c_854, c_32])).
% 3.19/1.55  tff(c_40, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_3'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.19/1.55  tff(c_880, plain, (k2_xboole_0('#skF_2', k2_tarski('#skF_1', '#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_860, c_40])).
% 3.19/1.55  tff(c_1167, plain, (~r2_hidden('#skF_3', '#skF_2') | ~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_401, c_880])).
% 3.19/1.55  tff(c_1171, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_1167])).
% 3.19/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.55  
% 3.19/1.55  Inference rules
% 3.19/1.55  ----------------------
% 3.19/1.55  #Ref     : 0
% 3.19/1.55  #Sup     : 286
% 3.19/1.55  #Fact    : 0
% 3.19/1.55  #Define  : 0
% 3.19/1.55  #Split   : 0
% 3.19/1.55  #Chain   : 0
% 3.19/1.55  #Close   : 0
% 3.19/1.55  
% 3.19/1.55  Ordering : KBO
% 3.19/1.55  
% 3.19/1.55  Simplification rules
% 3.19/1.55  ----------------------
% 3.19/1.55  #Subsume      : 23
% 3.19/1.55  #Demod        : 78
% 3.19/1.55  #Tautology    : 139
% 3.19/1.55  #SimpNegUnit  : 0
% 3.19/1.55  #BackRed      : 1
% 3.19/1.55  
% 3.19/1.55  #Partial instantiations: 0
% 3.19/1.55  #Strategies tried      : 1
% 3.19/1.55  
% 3.19/1.55  Timing (in seconds)
% 3.19/1.55  ----------------------
% 3.19/1.55  Preprocessing        : 0.34
% 3.19/1.55  Parsing              : 0.18
% 3.19/1.55  CNF conversion       : 0.02
% 3.19/1.55  Main loop            : 0.40
% 3.19/1.55  Inferencing          : 0.17
% 3.19/1.55  Reduction            : 0.14
% 3.19/1.55  Demodulation         : 0.11
% 3.19/1.55  BG Simplification    : 0.03
% 3.19/1.55  Subsumption          : 0.05
% 3.19/1.55  Abstraction          : 0.03
% 3.19/1.55  MUC search           : 0.00
% 3.19/1.55  Cooper               : 0.00
% 3.19/1.55  Total                : 0.77
% 3.19/1.55  Index Insertion      : 0.00
% 3.19/1.55  Index Deletion       : 0.00
% 3.19/1.55  Index Matching       : 0.00
% 3.19/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
