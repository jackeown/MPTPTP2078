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
% DateTime   : Thu Dec  3 09:50:32 EST 2020

% Result     : Theorem 4.87s
% Output     : CNFRefutation 4.87s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 122 expanded)
%              Number of leaves         :   30 (  53 expanded)
%              Depth                    :    9
%              Number of atoms          :   81 ( 156 expanded)
%              Number of equality atoms :   36 (  80 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_72,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_64,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_58,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_60,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
     => ~ r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_58,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_77,plain,(
    ! [A_57,B_58] : k1_enumset1(A_57,A_57,B_58) = k2_tarski(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_14,plain,(
    ! [E_11,A_5,C_7] : r2_hidden(E_11,k1_enumset1(A_5,E_11,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_83,plain,(
    ! [A_57,B_58] : r2_hidden(A_57,k2_tarski(A_57,B_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_14])).

tff(c_106,plain,(
    ! [A_64,B_65] : k3_tarski(k2_tarski(A_64,B_65)) = k2_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_48,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(A_33,k3_tarski(B_34))
      | ~ r2_hidden(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2540,plain,(
    ! [A_288,A_289,B_290] :
      ( r1_tarski(A_288,k2_xboole_0(A_289,B_290))
      | ~ r2_hidden(A_288,k2_tarski(A_289,B_290)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_48])).

tff(c_2567,plain,(
    ! [A_57,B_58] : r1_tarski(A_57,k2_xboole_0(A_57,B_58)) ),
    inference(resolution,[status(thm)],[c_83,c_2540])).

tff(c_369,plain,(
    ! [D_108,C_109,B_110,A_111] : k2_enumset1(D_108,C_109,B_110,A_111) = k2_enumset1(A_111,B_110,C_109,D_108) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_44,plain,(
    ! [A_26,B_27,C_28] : k2_enumset1(A_26,A_26,B_27,C_28) = k1_enumset1(A_26,B_27,C_28) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_385,plain,(
    ! [D_108,C_109,B_110] : k2_enumset1(D_108,C_109,B_110,B_110) = k1_enumset1(B_110,C_109,D_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_369,c_44])).

tff(c_38,plain,(
    ! [A_20,B_21,C_22] : k2_xboole_0(k2_tarski(A_20,B_21),k1_tarski(C_22)) = k1_enumset1(A_20,B_21,C_22) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_40,plain,(
    ! [A_23] : k2_tarski(A_23,A_23) = k1_tarski(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_807,plain,(
    ! [A_150,B_151,C_152,D_153] : k2_xboole_0(k2_tarski(A_150,B_151),k2_tarski(C_152,D_153)) = k2_enumset1(A_150,B_151,C_152,D_153) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_839,plain,(
    ! [A_150,B_151,A_23] : k2_xboole_0(k2_tarski(A_150,B_151),k1_tarski(A_23)) = k2_enumset1(A_150,B_151,A_23,A_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_807])).

tff(c_974,plain,(
    ! [A_180,B_179,A_178] : k1_enumset1(A_180,B_179,A_178) = k1_enumset1(A_178,B_179,A_180) ),
    inference(demodulation,[status(thm),theory(equality)],[c_385,c_38,c_839])).

tff(c_42,plain,(
    ! [A_24,B_25] : k1_enumset1(A_24,A_24,B_25) = k2_tarski(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1020,plain,(
    ! [A_180,B_179] : k1_enumset1(A_180,B_179,B_179) = k2_tarski(B_179,A_180) ),
    inference(superposition,[status(thm),theory(equality)],[c_974,c_42])).

tff(c_772,plain,(
    ! [D_147,C_148,B_149] : k2_enumset1(D_147,C_148,B_149,B_149) = k1_enumset1(B_149,C_148,D_147) ),
    inference(superposition,[status(thm),theory(equality)],[c_369,c_44])).

tff(c_785,plain,(
    ! [C_148,B_149] : k1_enumset1(C_148,B_149,B_149) = k1_enumset1(B_149,C_148,C_148) ),
    inference(superposition,[status(thm),theory(equality)],[c_772,c_44])).

tff(c_1153,plain,(
    ! [C_187,B_188] : k2_tarski(C_187,B_188) = k2_tarski(B_188,C_187) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1020,c_1020,c_785])).

tff(c_50,plain,(
    ! [A_35,B_36] : k3_tarski(k2_tarski(A_35,B_36)) = k2_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1304,plain,(
    ! [C_189,B_190] : k3_tarski(k2_tarski(C_189,B_190)) = k2_xboole_0(B_190,C_189) ),
    inference(superposition,[status(thm),theory(equality)],[c_1153,c_50])).

tff(c_1310,plain,(
    ! [C_189,B_190] : k2_xboole_0(C_189,B_190) = k2_xboole_0(B_190,C_189) ),
    inference(superposition,[status(thm),theory(equality)],[c_1304,c_50])).

tff(c_60,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_3'),'#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r2_xboole_0(A_3,B_4)
      | B_4 = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_156,plain,(
    ! [A_72,B_73] :
      ( r2_xboole_0(A_72,B_73)
      | B_73 = A_72
      | ~ r1_tarski(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_xboole_0(B_2,A_1)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_179,plain,(
    ! [B_77,A_78] :
      ( ~ r2_xboole_0(B_77,A_78)
      | B_77 = A_78
      | ~ r1_tarski(A_78,B_77) ) ),
    inference(resolution,[status(thm)],[c_156,c_2])).

tff(c_254,plain,(
    ! [B_89,A_90] :
      ( ~ r1_tarski(B_89,A_90)
      | B_89 = A_90
      | ~ r1_tarski(A_90,B_89) ) ),
    inference(resolution,[status(thm)],[c_4,c_179])).

tff(c_260,plain,
    ( k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') = '#skF_4'
    | ~ r1_tarski('#skF_4',k2_xboole_0(k1_tarski('#skF_3'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_60,c_254])).

tff(c_261,plain,(
    ~ r1_tarski('#skF_4',k2_xboole_0(k1_tarski('#skF_3'),'#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_260])).

tff(c_1333,plain,(
    ~ r1_tarski('#skF_4',k2_xboole_0('#skF_4',k1_tarski('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1310,c_261])).

tff(c_2618,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2567,c_1333])).

tff(c_2619,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_260])).

tff(c_141,plain,(
    ! [B_67,C_68,A_69] :
      ( r2_hidden(B_67,C_68)
      | ~ r1_tarski(k2_tarski(A_69,B_67),C_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_150,plain,(
    ! [A_70,C_71] :
      ( r2_hidden(A_70,C_71)
      | ~ r1_tarski(k1_tarski(A_70),C_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_141])).

tff(c_184,plain,(
    ! [A_79,B_80] :
      ( r2_hidden(A_79,k3_tarski(B_80))
      | ~ r2_hidden(k1_tarski(A_79),B_80) ) ),
    inference(resolution,[status(thm)],[c_48,c_150])).

tff(c_196,plain,(
    ! [A_79,B_58] : r2_hidden(A_79,k3_tarski(k2_tarski(k1_tarski(A_79),B_58))) ),
    inference(resolution,[status(thm)],[c_83,c_184])).

tff(c_213,plain,(
    ! [A_79,B_58] : r2_hidden(A_79,k2_xboole_0(k1_tarski(A_79),B_58)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_196])).

tff(c_2625,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2619,c_213])).

tff(c_2629,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2625])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:32:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.87/2.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.87/2.30  
% 4.87/2.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.87/2.30  %$ r2_xboole_0 > r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.87/2.30  
% 4.87/2.30  %Foreground sorts:
% 4.87/2.30  
% 4.87/2.30  
% 4.87/2.30  %Background operators:
% 4.87/2.30  
% 4.87/2.30  
% 4.87/2.30  %Foreground operators:
% 4.87/2.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.87/2.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.87/2.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.87/2.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.87/2.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.87/2.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.87/2.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.87/2.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 4.87/2.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.87/2.30  tff('#skF_3', type, '#skF_3': $i).
% 4.87/2.30  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 4.87/2.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.87/2.30  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.87/2.30  tff('#skF_4', type, '#skF_4': $i).
% 4.87/2.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.87/2.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.87/2.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 4.87/2.30  
% 4.87/2.33  tff(f_83, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 4.87/2.33  tff(f_62, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 4.87/2.33  tff(f_52, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 4.87/2.33  tff(f_72, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.87/2.33  tff(f_70, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 4.87/2.33  tff(f_56, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_enumset1)).
% 4.87/2.33  tff(f_64, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 4.87/2.33  tff(f_58, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 4.87/2.33  tff(f_60, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.87/2.33  tff(f_54, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 4.87/2.33  tff(f_37, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 4.87/2.33  tff(f_30, axiom, (![A, B]: (r2_xboole_0(A, B) => ~r2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_xboole_0)).
% 4.87/2.33  tff(f_78, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 4.87/2.33  tff(c_58, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.87/2.33  tff(c_77, plain, (![A_57, B_58]: (k1_enumset1(A_57, A_57, B_58)=k2_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.87/2.33  tff(c_14, plain, (![E_11, A_5, C_7]: (r2_hidden(E_11, k1_enumset1(A_5, E_11, C_7)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.87/2.33  tff(c_83, plain, (![A_57, B_58]: (r2_hidden(A_57, k2_tarski(A_57, B_58)))), inference(superposition, [status(thm), theory('equality')], [c_77, c_14])).
% 4.87/2.33  tff(c_106, plain, (![A_64, B_65]: (k3_tarski(k2_tarski(A_64, B_65))=k2_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.87/2.33  tff(c_48, plain, (![A_33, B_34]: (r1_tarski(A_33, k3_tarski(B_34)) | ~r2_hidden(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.87/2.33  tff(c_2540, plain, (![A_288, A_289, B_290]: (r1_tarski(A_288, k2_xboole_0(A_289, B_290)) | ~r2_hidden(A_288, k2_tarski(A_289, B_290)))), inference(superposition, [status(thm), theory('equality')], [c_106, c_48])).
% 4.87/2.33  tff(c_2567, plain, (![A_57, B_58]: (r1_tarski(A_57, k2_xboole_0(A_57, B_58)))), inference(resolution, [status(thm)], [c_83, c_2540])).
% 4.87/2.33  tff(c_369, plain, (![D_108, C_109, B_110, A_111]: (k2_enumset1(D_108, C_109, B_110, A_111)=k2_enumset1(A_111, B_110, C_109, D_108))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.87/2.33  tff(c_44, plain, (![A_26, B_27, C_28]: (k2_enumset1(A_26, A_26, B_27, C_28)=k1_enumset1(A_26, B_27, C_28))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.87/2.33  tff(c_385, plain, (![D_108, C_109, B_110]: (k2_enumset1(D_108, C_109, B_110, B_110)=k1_enumset1(B_110, C_109, D_108))), inference(superposition, [status(thm), theory('equality')], [c_369, c_44])).
% 4.87/2.33  tff(c_38, plain, (![A_20, B_21, C_22]: (k2_xboole_0(k2_tarski(A_20, B_21), k1_tarski(C_22))=k1_enumset1(A_20, B_21, C_22))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.87/2.33  tff(c_40, plain, (![A_23]: (k2_tarski(A_23, A_23)=k1_tarski(A_23))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.87/2.33  tff(c_807, plain, (![A_150, B_151, C_152, D_153]: (k2_xboole_0(k2_tarski(A_150, B_151), k2_tarski(C_152, D_153))=k2_enumset1(A_150, B_151, C_152, D_153))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.87/2.33  tff(c_839, plain, (![A_150, B_151, A_23]: (k2_xboole_0(k2_tarski(A_150, B_151), k1_tarski(A_23))=k2_enumset1(A_150, B_151, A_23, A_23))), inference(superposition, [status(thm), theory('equality')], [c_40, c_807])).
% 4.87/2.33  tff(c_974, plain, (![A_180, B_179, A_178]: (k1_enumset1(A_180, B_179, A_178)=k1_enumset1(A_178, B_179, A_180))), inference(demodulation, [status(thm), theory('equality')], [c_385, c_38, c_839])).
% 4.87/2.33  tff(c_42, plain, (![A_24, B_25]: (k1_enumset1(A_24, A_24, B_25)=k2_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.87/2.33  tff(c_1020, plain, (![A_180, B_179]: (k1_enumset1(A_180, B_179, B_179)=k2_tarski(B_179, A_180))), inference(superposition, [status(thm), theory('equality')], [c_974, c_42])).
% 4.87/2.33  tff(c_772, plain, (![D_147, C_148, B_149]: (k2_enumset1(D_147, C_148, B_149, B_149)=k1_enumset1(B_149, C_148, D_147))), inference(superposition, [status(thm), theory('equality')], [c_369, c_44])).
% 4.87/2.33  tff(c_785, plain, (![C_148, B_149]: (k1_enumset1(C_148, B_149, B_149)=k1_enumset1(B_149, C_148, C_148))), inference(superposition, [status(thm), theory('equality')], [c_772, c_44])).
% 4.87/2.33  tff(c_1153, plain, (![C_187, B_188]: (k2_tarski(C_187, B_188)=k2_tarski(B_188, C_187))), inference(demodulation, [status(thm), theory('equality')], [c_1020, c_1020, c_785])).
% 4.87/2.33  tff(c_50, plain, (![A_35, B_36]: (k3_tarski(k2_tarski(A_35, B_36))=k2_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.87/2.33  tff(c_1304, plain, (![C_189, B_190]: (k3_tarski(k2_tarski(C_189, B_190))=k2_xboole_0(B_190, C_189))), inference(superposition, [status(thm), theory('equality')], [c_1153, c_50])).
% 4.87/2.33  tff(c_1310, plain, (![C_189, B_190]: (k2_xboole_0(C_189, B_190)=k2_xboole_0(B_190, C_189))), inference(superposition, [status(thm), theory('equality')], [c_1304, c_50])).
% 4.87/2.33  tff(c_60, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_3'), '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.87/2.33  tff(c_4, plain, (![A_3, B_4]: (r2_xboole_0(A_3, B_4) | B_4=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.87/2.33  tff(c_156, plain, (![A_72, B_73]: (r2_xboole_0(A_72, B_73) | B_73=A_72 | ~r1_tarski(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.87/2.33  tff(c_2, plain, (![B_2, A_1]: (~r2_xboole_0(B_2, A_1) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.87/2.33  tff(c_179, plain, (![B_77, A_78]: (~r2_xboole_0(B_77, A_78) | B_77=A_78 | ~r1_tarski(A_78, B_77))), inference(resolution, [status(thm)], [c_156, c_2])).
% 4.87/2.33  tff(c_254, plain, (![B_89, A_90]: (~r1_tarski(B_89, A_90) | B_89=A_90 | ~r1_tarski(A_90, B_89))), inference(resolution, [status(thm)], [c_4, c_179])).
% 4.87/2.33  tff(c_260, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')='#skF_4' | ~r1_tarski('#skF_4', k2_xboole_0(k1_tarski('#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_60, c_254])).
% 4.87/2.33  tff(c_261, plain, (~r1_tarski('#skF_4', k2_xboole_0(k1_tarski('#skF_3'), '#skF_4'))), inference(splitLeft, [status(thm)], [c_260])).
% 4.87/2.33  tff(c_1333, plain, (~r1_tarski('#skF_4', k2_xboole_0('#skF_4', k1_tarski('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1310, c_261])).
% 4.87/2.33  tff(c_2618, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2567, c_1333])).
% 4.87/2.33  tff(c_2619, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_260])).
% 4.87/2.33  tff(c_141, plain, (![B_67, C_68, A_69]: (r2_hidden(B_67, C_68) | ~r1_tarski(k2_tarski(A_69, B_67), C_68))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.87/2.33  tff(c_150, plain, (![A_70, C_71]: (r2_hidden(A_70, C_71) | ~r1_tarski(k1_tarski(A_70), C_71))), inference(superposition, [status(thm), theory('equality')], [c_40, c_141])).
% 4.87/2.33  tff(c_184, plain, (![A_79, B_80]: (r2_hidden(A_79, k3_tarski(B_80)) | ~r2_hidden(k1_tarski(A_79), B_80))), inference(resolution, [status(thm)], [c_48, c_150])).
% 4.87/2.33  tff(c_196, plain, (![A_79, B_58]: (r2_hidden(A_79, k3_tarski(k2_tarski(k1_tarski(A_79), B_58))))), inference(resolution, [status(thm)], [c_83, c_184])).
% 4.87/2.33  tff(c_213, plain, (![A_79, B_58]: (r2_hidden(A_79, k2_xboole_0(k1_tarski(A_79), B_58)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_196])).
% 4.87/2.33  tff(c_2625, plain, (r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2619, c_213])).
% 4.87/2.33  tff(c_2629, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_2625])).
% 4.87/2.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.87/2.33  
% 4.87/2.33  Inference rules
% 4.87/2.33  ----------------------
% 4.87/2.33  #Ref     : 0
% 4.87/2.33  #Sup     : 564
% 4.87/2.33  #Fact    : 0
% 4.87/2.33  #Define  : 0
% 4.87/2.33  #Split   : 1
% 4.87/2.33  #Chain   : 0
% 4.87/2.33  #Close   : 0
% 4.87/2.33  
% 4.87/2.33  Ordering : KBO
% 4.87/2.33  
% 4.87/2.33  Simplification rules
% 4.87/2.33  ----------------------
% 4.87/2.33  #Subsume      : 21
% 4.87/2.33  #Demod        : 317
% 4.87/2.33  #Tautology    : 309
% 4.87/2.33  #SimpNegUnit  : 1
% 4.87/2.33  #BackRed      : 5
% 4.87/2.33  
% 4.87/2.33  #Partial instantiations: 0
% 4.87/2.33  #Strategies tried      : 1
% 4.87/2.33  
% 4.87/2.33  Timing (in seconds)
% 4.87/2.33  ----------------------
% 4.87/2.33  Preprocessing        : 0.52
% 4.87/2.33  Parsing              : 0.25
% 4.87/2.33  CNF conversion       : 0.04
% 4.87/2.33  Main loop            : 0.89
% 4.87/2.33  Inferencing          : 0.29
% 4.87/2.33  Reduction            : 0.33
% 4.87/2.33  Demodulation         : 0.25
% 4.87/2.33  BG Simplification    : 0.04
% 4.87/2.33  Subsumption          : 0.17
% 4.87/2.33  Abstraction          : 0.04
% 4.87/2.33  MUC search           : 0.00
% 4.87/2.33  Cooper               : 0.00
% 4.87/2.33  Total                : 1.47
% 4.87/2.33  Index Insertion      : 0.00
% 4.87/2.33  Index Deletion       : 0.00
% 4.87/2.33  Index Matching       : 0.00
% 4.87/2.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
