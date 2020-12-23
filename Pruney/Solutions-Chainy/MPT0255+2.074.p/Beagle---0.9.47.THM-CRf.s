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
% DateTime   : Thu Dec  3 09:51:49 EST 2020

% Result     : Theorem 3.77s
% Output     : CNFRefutation 3.97s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 250 expanded)
%              Number of leaves         :   25 (  95 expanded)
%              Depth                    :   12
%              Number of atoms          :   77 ( 358 expanded)
%              Number of equality atoms :   33 ( 178 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(f_42,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_63,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_46,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(c_24,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_111,plain,(
    ! [A_30,B_31] :
      ( k2_xboole_0(A_30,B_31) = B_31
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_116,plain,(
    ! [A_32] : k2_xboole_0(k1_xboole_0,A_32) = A_32 ),
    inference(resolution,[status(thm)],[c_24,c_111])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_122,plain,(
    ! [A_32] : k2_xboole_0(A_32,k1_xboole_0) = A_32 ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_2])).

tff(c_20,plain,(
    ! [A_3,B_4,C_5] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_5),B_4)
      | r2_hidden('#skF_1'(A_3,B_4,C_5),A_3)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k2_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_309,plain,(
    ! [A_63,B_64] : k2_xboole_0(k1_tarski(A_63),k1_tarski(B_64)) = k2_tarski(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_397,plain,(
    ! [B_71,A_72] : k2_xboole_0(k1_tarski(B_71),k1_tarski(A_72)) = k2_tarski(A_72,B_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_2])).

tff(c_26,plain,(
    ! [A_12,B_13] : k2_xboole_0(k1_tarski(A_12),k1_tarski(B_13)) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_406,plain,(
    ! [B_71,A_72] : k2_tarski(B_71,A_72) = k2_tarski(A_72,B_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_397,c_26])).

tff(c_42,plain,(
    k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_469,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_3'),'#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_42])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | r2_hidden(D_8,k2_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_28,plain,(
    ! [A_14] : k2_tarski(A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_451,plain,(
    ! [A_73,B_74,C_75] :
      ( r1_tarski(k2_tarski(A_73,B_74),C_75)
      | ~ r2_hidden(B_74,C_75)
      | ~ r2_hidden(A_73,C_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_711,plain,(
    ! [A_100,C_101] :
      ( r1_tarski(k1_tarski(A_100),C_101)
      | ~ r2_hidden(A_100,C_101)
      | ~ r2_hidden(A_100,C_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_451])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_720,plain,(
    ! [A_102,C_103] :
      ( k2_xboole_0(k1_tarski(A_102),C_103) = C_103
      | ~ r2_hidden(A_102,C_103) ) ),
    inference(resolution,[status(thm)],[c_711,c_22])).

tff(c_40,plain,(
    ! [A_22,B_23] : k2_xboole_0(k1_tarski(A_22),B_23) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1075,plain,(
    ! [C_114,A_115] :
      ( k1_xboole_0 != C_114
      | ~ r2_hidden(A_115,C_114) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_720,c_40])).

tff(c_1121,plain,(
    ! [A_118,B_119,D_120] :
      ( k2_xboole_0(A_118,B_119) != k1_xboole_0
      | ~ r2_hidden(D_120,B_119) ) ),
    inference(resolution,[status(thm)],[c_6,c_1075])).

tff(c_1144,plain,(
    ! [D_121] : ~ r2_hidden(D_121,'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_469,c_1121])).

tff(c_2014,plain,(
    ! [A_154,C_155] :
      ( r2_hidden('#skF_1'(A_154,'#skF_5',C_155),A_154)
      | r2_hidden('#skF_2'(A_154,'#skF_5',C_155),C_155)
      | k2_xboole_0(A_154,'#skF_5') = C_155 ) ),
    inference(resolution,[status(thm)],[c_20,c_1144])).

tff(c_139,plain,(
    ! [A_33] : k2_xboole_0(A_33,k1_xboole_0) = A_33 ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_2])).

tff(c_156,plain,(
    ! [A_22] : k1_tarski(A_22) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_40])).

tff(c_752,plain,(
    ! [A_102] :
      ( k1_tarski(A_102) = k1_xboole_0
      | ~ r2_hidden(A_102,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_720,c_122])).

tff(c_788,plain,(
    ! [A_102] : ~ r2_hidden(A_102,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_156,c_752])).

tff(c_2056,plain,(
    ! [C_155] :
      ( r2_hidden('#skF_2'(k1_xboole_0,'#skF_5',C_155),C_155)
      | k2_xboole_0(k1_xboole_0,'#skF_5') = C_155 ) ),
    inference(resolution,[status(thm)],[c_2014,c_788])).

tff(c_2153,plain,(
    ! [C_156] :
      ( r2_hidden('#skF_2'(k1_xboole_0,'#skF_5',C_156),C_156)
      | C_156 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_2,c_2056])).

tff(c_2218,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_2153,c_788])).

tff(c_2230,plain,(
    ! [A_22] : k1_tarski(A_22) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2218,c_156])).

tff(c_665,plain,(
    ! [D_93,B_94,A_95] :
      ( ~ r2_hidden(D_93,k1_tarski(B_94))
      | r2_hidden(D_93,k2_tarski(A_95,B_94)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_6])).

tff(c_254,plain,(
    ! [D_48,A_49,B_50] :
      ( ~ r2_hidden(D_48,A_49)
      | r2_hidden(D_48,k2_xboole_0(A_49,B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_275,plain,(
    ! [D_48] :
      ( ~ r2_hidden(D_48,k2_tarski('#skF_3','#skF_4'))
      | r2_hidden(D_48,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_254])).

tff(c_467,plain,(
    ! [D_48] :
      ( ~ r2_hidden(D_48,k2_tarski('#skF_4','#skF_3'))
      | r2_hidden(D_48,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_275])).

tff(c_687,plain,(
    ! [D_93] :
      ( r2_hidden(D_93,k1_xboole_0)
      | ~ r2_hidden(D_93,k1_tarski('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_665,c_467])).

tff(c_891,plain,(
    ! [D_93] : ~ r2_hidden(D_93,k1_tarski('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_788,c_687])).

tff(c_2217,plain,(
    k1_tarski('#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_2153,c_891])).

tff(c_2345,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2230,c_2217])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:24:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.77/1.72  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/1.73  
% 3.77/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/1.73  %$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 3.77/1.73  
% 3.77/1.73  %Foreground sorts:
% 3.77/1.73  
% 3.77/1.73  
% 3.77/1.73  %Background operators:
% 3.77/1.73  
% 3.77/1.73  
% 3.77/1.73  %Foreground operators:
% 3.77/1.73  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.77/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.77/1.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.77/1.73  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.77/1.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.77/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.77/1.73  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.77/1.73  tff('#skF_5', type, '#skF_5': $i).
% 3.77/1.73  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.77/1.73  tff('#skF_3', type, '#skF_3': $i).
% 3.77/1.73  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.77/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.77/1.73  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.77/1.73  tff('#skF_4', type, '#skF_4': $i).
% 3.77/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.77/1.73  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.77/1.73  
% 3.97/1.74  tff(f_42, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.97/1.74  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.97/1.74  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.97/1.74  tff(f_36, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 3.97/1.74  tff(f_44, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 3.97/1.74  tff(f_63, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 3.97/1.74  tff(f_46, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.97/1.74  tff(f_56, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.97/1.74  tff(f_59, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.97/1.74  tff(c_24, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.97/1.74  tff(c_111, plain, (![A_30, B_31]: (k2_xboole_0(A_30, B_31)=B_31 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.97/1.74  tff(c_116, plain, (![A_32]: (k2_xboole_0(k1_xboole_0, A_32)=A_32)), inference(resolution, [status(thm)], [c_24, c_111])).
% 3.97/1.74  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.97/1.74  tff(c_122, plain, (![A_32]: (k2_xboole_0(A_32, k1_xboole_0)=A_32)), inference(superposition, [status(thm), theory('equality')], [c_116, c_2])).
% 3.97/1.74  tff(c_20, plain, (![A_3, B_4, C_5]: (r2_hidden('#skF_1'(A_3, B_4, C_5), B_4) | r2_hidden('#skF_1'(A_3, B_4, C_5), A_3) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k2_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.97/1.74  tff(c_309, plain, (![A_63, B_64]: (k2_xboole_0(k1_tarski(A_63), k1_tarski(B_64))=k2_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.97/1.74  tff(c_397, plain, (![B_71, A_72]: (k2_xboole_0(k1_tarski(B_71), k1_tarski(A_72))=k2_tarski(A_72, B_71))), inference(superposition, [status(thm), theory('equality')], [c_309, c_2])).
% 3.97/1.74  tff(c_26, plain, (![A_12, B_13]: (k2_xboole_0(k1_tarski(A_12), k1_tarski(B_13))=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.97/1.74  tff(c_406, plain, (![B_71, A_72]: (k2_tarski(B_71, A_72)=k2_tarski(A_72, B_71))), inference(superposition, [status(thm), theory('equality')], [c_397, c_26])).
% 3.97/1.74  tff(c_42, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.97/1.74  tff(c_469, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_3'), '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_406, c_42])).
% 3.97/1.74  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | r2_hidden(D_8, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.97/1.74  tff(c_28, plain, (![A_14]: (k2_tarski(A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.97/1.74  tff(c_451, plain, (![A_73, B_74, C_75]: (r1_tarski(k2_tarski(A_73, B_74), C_75) | ~r2_hidden(B_74, C_75) | ~r2_hidden(A_73, C_75))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.97/1.74  tff(c_711, plain, (![A_100, C_101]: (r1_tarski(k1_tarski(A_100), C_101) | ~r2_hidden(A_100, C_101) | ~r2_hidden(A_100, C_101))), inference(superposition, [status(thm), theory('equality')], [c_28, c_451])).
% 3.97/1.74  tff(c_22, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.97/1.74  tff(c_720, plain, (![A_102, C_103]: (k2_xboole_0(k1_tarski(A_102), C_103)=C_103 | ~r2_hidden(A_102, C_103))), inference(resolution, [status(thm)], [c_711, c_22])).
% 3.97/1.74  tff(c_40, plain, (![A_22, B_23]: (k2_xboole_0(k1_tarski(A_22), B_23)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.97/1.74  tff(c_1075, plain, (![C_114, A_115]: (k1_xboole_0!=C_114 | ~r2_hidden(A_115, C_114))), inference(superposition, [status(thm), theory('equality')], [c_720, c_40])).
% 3.97/1.74  tff(c_1121, plain, (![A_118, B_119, D_120]: (k2_xboole_0(A_118, B_119)!=k1_xboole_0 | ~r2_hidden(D_120, B_119))), inference(resolution, [status(thm)], [c_6, c_1075])).
% 3.97/1.74  tff(c_1144, plain, (![D_121]: (~r2_hidden(D_121, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_469, c_1121])).
% 3.97/1.74  tff(c_2014, plain, (![A_154, C_155]: (r2_hidden('#skF_1'(A_154, '#skF_5', C_155), A_154) | r2_hidden('#skF_2'(A_154, '#skF_5', C_155), C_155) | k2_xboole_0(A_154, '#skF_5')=C_155)), inference(resolution, [status(thm)], [c_20, c_1144])).
% 3.97/1.74  tff(c_139, plain, (![A_33]: (k2_xboole_0(A_33, k1_xboole_0)=A_33)), inference(superposition, [status(thm), theory('equality')], [c_116, c_2])).
% 3.97/1.74  tff(c_156, plain, (![A_22]: (k1_tarski(A_22)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_139, c_40])).
% 3.97/1.74  tff(c_752, plain, (![A_102]: (k1_tarski(A_102)=k1_xboole_0 | ~r2_hidden(A_102, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_720, c_122])).
% 3.97/1.74  tff(c_788, plain, (![A_102]: (~r2_hidden(A_102, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_156, c_752])).
% 3.97/1.74  tff(c_2056, plain, (![C_155]: (r2_hidden('#skF_2'(k1_xboole_0, '#skF_5', C_155), C_155) | k2_xboole_0(k1_xboole_0, '#skF_5')=C_155)), inference(resolution, [status(thm)], [c_2014, c_788])).
% 3.97/1.74  tff(c_2153, plain, (![C_156]: (r2_hidden('#skF_2'(k1_xboole_0, '#skF_5', C_156), C_156) | C_156='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_2, c_2056])).
% 3.97/1.74  tff(c_2218, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_2153, c_788])).
% 3.97/1.74  tff(c_2230, plain, (![A_22]: (k1_tarski(A_22)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2218, c_156])).
% 3.97/1.74  tff(c_665, plain, (![D_93, B_94, A_95]: (~r2_hidden(D_93, k1_tarski(B_94)) | r2_hidden(D_93, k2_tarski(A_95, B_94)))), inference(superposition, [status(thm), theory('equality')], [c_309, c_6])).
% 3.97/1.74  tff(c_254, plain, (![D_48, A_49, B_50]: (~r2_hidden(D_48, A_49) | r2_hidden(D_48, k2_xboole_0(A_49, B_50)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.97/1.74  tff(c_275, plain, (![D_48]: (~r2_hidden(D_48, k2_tarski('#skF_3', '#skF_4')) | r2_hidden(D_48, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_42, c_254])).
% 3.97/1.74  tff(c_467, plain, (![D_48]: (~r2_hidden(D_48, k2_tarski('#skF_4', '#skF_3')) | r2_hidden(D_48, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_406, c_275])).
% 3.97/1.74  tff(c_687, plain, (![D_93]: (r2_hidden(D_93, k1_xboole_0) | ~r2_hidden(D_93, k1_tarski('#skF_3')))), inference(resolution, [status(thm)], [c_665, c_467])).
% 3.97/1.74  tff(c_891, plain, (![D_93]: (~r2_hidden(D_93, k1_tarski('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_788, c_687])).
% 3.97/1.74  tff(c_2217, plain, (k1_tarski('#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_2153, c_891])).
% 3.97/1.74  tff(c_2345, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2230, c_2217])).
% 3.97/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.97/1.74  
% 3.97/1.74  Inference rules
% 3.97/1.74  ----------------------
% 3.97/1.74  #Ref     : 0
% 3.97/1.74  #Sup     : 540
% 3.97/1.74  #Fact    : 6
% 3.97/1.74  #Define  : 0
% 3.97/1.74  #Split   : 0
% 3.97/1.74  #Chain   : 0
% 3.97/1.74  #Close   : 0
% 3.97/1.74  
% 3.97/1.74  Ordering : KBO
% 3.97/1.74  
% 3.97/1.74  Simplification rules
% 3.97/1.74  ----------------------
% 3.97/1.74  #Subsume      : 166
% 3.97/1.74  #Demod        : 115
% 3.97/1.74  #Tautology    : 128
% 3.97/1.74  #SimpNegUnit  : 17
% 3.97/1.74  #BackRed      : 26
% 3.97/1.74  
% 3.97/1.74  #Partial instantiations: 0
% 3.97/1.74  #Strategies tried      : 1
% 3.97/1.74  
% 3.97/1.74  Timing (in seconds)
% 3.97/1.74  ----------------------
% 3.97/1.75  Preprocessing        : 0.31
% 3.97/1.75  Parsing              : 0.16
% 3.97/1.75  CNF conversion       : 0.02
% 3.97/1.75  Main loop            : 0.61
% 3.97/1.75  Inferencing          : 0.21
% 3.97/1.75  Reduction            : 0.21
% 3.97/1.75  Demodulation         : 0.16
% 3.97/1.75  BG Simplification    : 0.03
% 3.97/1.75  Subsumption          : 0.12
% 3.97/1.75  Abstraction          : 0.03
% 4.02/1.75  MUC search           : 0.00
% 4.02/1.75  Cooper               : 0.00
% 4.02/1.75  Total                : 0.95
% 4.02/1.75  Index Insertion      : 0.00
% 4.02/1.75  Index Deletion       : 0.00
% 4.02/1.75  Index Matching       : 0.00
% 4.02/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
