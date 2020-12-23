%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:45 EST 2020

% Result     : Theorem 10.80s
% Output     : CNFRefutation 10.80s
% Verified   : 
% Statistics : Number of formulae       :   50 (  54 expanded)
%              Number of leaves         :   26 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   37 (  42 expanded)
%              Number of equality atoms :   28 (  32 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_88,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_112,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_110,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_76,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_117,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k4_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_234,plain,(
    ! [B_90,A_91] : k5_xboole_0(B_90,A_91) = k5_xboole_0(A_91,B_90) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_50,plain,(
    ! [A_48] : k5_xboole_0(A_48,k1_xboole_0) = A_48 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_250,plain,(
    ! [A_91] : k5_xboole_0(k1_xboole_0,A_91) = A_91 ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_50])).

tff(c_66,plain,(
    ! [A_63] : k5_xboole_0(A_63,A_63) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1758,plain,(
    ! [A_164,B_165,C_166] : k5_xboole_0(k5_xboole_0(A_164,B_165),C_166) = k5_xboole_0(A_164,k5_xboole_0(B_165,C_166)) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1804,plain,(
    ! [A_63,C_166] : k5_xboole_0(A_63,k5_xboole_0(A_63,C_166)) = k5_xboole_0(k1_xboole_0,C_166) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_1758])).

tff(c_1822,plain,(
    ! [A_63,C_166] : k5_xboole_0(A_63,k5_xboole_0(A_63,C_166)) = C_166 ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_1804])).

tff(c_2257,plain,(
    ! [A_179,B_180] : k4_xboole_0(k2_xboole_0(A_179,B_180),k3_xboole_0(A_179,B_180)) = k5_xboole_0(A_179,B_180) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_10110,plain,(
    ! [B_392,A_393] : k4_xboole_0(k2_xboole_0(B_392,A_393),k3_xboole_0(A_393,B_392)) = k5_xboole_0(A_393,B_392) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2257])).

tff(c_32,plain,(
    ! [A_29,B_30] : r1_tarski(k4_xboole_0(A_29,B_30),A_29) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_355,plain,(
    ! [A_98,B_99] :
      ( k4_xboole_0(A_98,B_99) = k1_xboole_0
      | ~ r1_tarski(A_98,B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_369,plain,(
    ! [A_29,B_30] : k4_xboole_0(k4_xboole_0(A_29,B_30),A_29) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_355])).

tff(c_15841,plain,(
    ! [A_521,B_522] : k4_xboole_0(k5_xboole_0(A_521,B_522),k2_xboole_0(B_522,A_521)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10110,c_369])).

tff(c_16066,plain,(
    ! [C_166,A_63] : k4_xboole_0(C_166,k2_xboole_0(k5_xboole_0(A_63,C_166),A_63)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1822,c_15841])).

tff(c_16159,plain,(
    ! [C_166,A_63] : k4_xboole_0(C_166,k2_xboole_0(A_63,k5_xboole_0(A_63,C_166))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_16066])).

tff(c_38,plain,(
    ! [A_34,B_35,C_36] : k4_xboole_0(k4_xboole_0(A_34,B_35),C_36) = k4_xboole_0(A_34,k2_xboole_0(B_35,C_36)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_649,plain,(
    ! [A_114,B_115] :
      ( r1_tarski(A_114,B_115)
      | k4_xboole_0(A_114,B_115) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_70,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_3','#skF_4'),k5_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_72,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_3','#skF_4'),k5_xboole_0('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_70])).

tff(c_657,plain,(
    k4_xboole_0(k4_xboole_0('#skF_3','#skF_4'),k5_xboole_0('#skF_4','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_649,c_72])).

tff(c_1370,plain,(
    k4_xboole_0('#skF_3',k2_xboole_0('#skF_4',k5_xboole_0('#skF_4','#skF_3'))) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_657])).

tff(c_27411,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16159,c_1370])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:29:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.80/4.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.80/4.67  
% 10.80/4.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.80/4.67  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 10.80/4.67  
% 10.80/4.67  %Foreground sorts:
% 10.80/4.67  
% 10.80/4.67  
% 10.80/4.67  %Background operators:
% 10.80/4.67  
% 10.80/4.67  
% 10.80/4.67  %Foreground operators:
% 10.80/4.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.80/4.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.80/4.67  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.80/4.67  tff('#skF_1', type, '#skF_1': $i > $i).
% 10.80/4.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.80/4.67  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.80/4.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.80/4.67  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.80/4.67  tff('#skF_3', type, '#skF_3': $i).
% 10.80/4.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.80/4.67  tff('#skF_4', type, '#skF_4': $i).
% 10.80/4.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.80/4.67  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.80/4.67  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.80/4.67  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.80/4.67  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.80/4.67  
% 10.80/4.68  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 10.80/4.68  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 10.80/4.68  tff(f_88, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 10.80/4.68  tff(f_112, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 10.80/4.68  tff(f_110, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 10.80/4.68  tff(f_62, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l98_xboole_1)).
% 10.80/4.68  tff(f_70, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 10.80/4.68  tff(f_60, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 10.80/4.68  tff(f_76, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 10.80/4.68  tff(f_117, negated_conjecture, ~(![A, B]: r1_tarski(k4_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_xboole_1)).
% 10.80/4.68  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.80/4.68  tff(c_234, plain, (![B_90, A_91]: (k5_xboole_0(B_90, A_91)=k5_xboole_0(A_91, B_90))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.80/4.68  tff(c_50, plain, (![A_48]: (k5_xboole_0(A_48, k1_xboole_0)=A_48)), inference(cnfTransformation, [status(thm)], [f_88])).
% 10.80/4.68  tff(c_250, plain, (![A_91]: (k5_xboole_0(k1_xboole_0, A_91)=A_91)), inference(superposition, [status(thm), theory('equality')], [c_234, c_50])).
% 10.80/4.68  tff(c_66, plain, (![A_63]: (k5_xboole_0(A_63, A_63)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_112])).
% 10.80/4.68  tff(c_1758, plain, (![A_164, B_165, C_166]: (k5_xboole_0(k5_xboole_0(A_164, B_165), C_166)=k5_xboole_0(A_164, k5_xboole_0(B_165, C_166)))), inference(cnfTransformation, [status(thm)], [f_110])).
% 10.80/4.68  tff(c_1804, plain, (![A_63, C_166]: (k5_xboole_0(A_63, k5_xboole_0(A_63, C_166))=k5_xboole_0(k1_xboole_0, C_166))), inference(superposition, [status(thm), theory('equality')], [c_66, c_1758])).
% 10.80/4.68  tff(c_1822, plain, (![A_63, C_166]: (k5_xboole_0(A_63, k5_xboole_0(A_63, C_166))=C_166)), inference(demodulation, [status(thm), theory('equality')], [c_250, c_1804])).
% 10.80/4.68  tff(c_2257, plain, (![A_179, B_180]: (k4_xboole_0(k2_xboole_0(A_179, B_180), k3_xboole_0(A_179, B_180))=k5_xboole_0(A_179, B_180))), inference(cnfTransformation, [status(thm)], [f_62])).
% 10.80/4.68  tff(c_10110, plain, (![B_392, A_393]: (k4_xboole_0(k2_xboole_0(B_392, A_393), k3_xboole_0(A_393, B_392))=k5_xboole_0(A_393, B_392))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2257])).
% 10.80/4.68  tff(c_32, plain, (![A_29, B_30]: (r1_tarski(k4_xboole_0(A_29, B_30), A_29))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.80/4.68  tff(c_355, plain, (![A_98, B_99]: (k4_xboole_0(A_98, B_99)=k1_xboole_0 | ~r1_tarski(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.80/4.68  tff(c_369, plain, (![A_29, B_30]: (k4_xboole_0(k4_xboole_0(A_29, B_30), A_29)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_355])).
% 10.80/4.68  tff(c_15841, plain, (![A_521, B_522]: (k4_xboole_0(k5_xboole_0(A_521, B_522), k2_xboole_0(B_522, A_521))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10110, c_369])).
% 10.80/4.68  tff(c_16066, plain, (![C_166, A_63]: (k4_xboole_0(C_166, k2_xboole_0(k5_xboole_0(A_63, C_166), A_63))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1822, c_15841])).
% 10.80/4.68  tff(c_16159, plain, (![C_166, A_63]: (k4_xboole_0(C_166, k2_xboole_0(A_63, k5_xboole_0(A_63, C_166)))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_16066])).
% 10.80/4.68  tff(c_38, plain, (![A_34, B_35, C_36]: (k4_xboole_0(k4_xboole_0(A_34, B_35), C_36)=k4_xboole_0(A_34, k2_xboole_0(B_35, C_36)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.80/4.68  tff(c_649, plain, (![A_114, B_115]: (r1_tarski(A_114, B_115) | k4_xboole_0(A_114, B_115)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.80/4.68  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.80/4.68  tff(c_70, plain, (~r1_tarski(k4_xboole_0('#skF_3', '#skF_4'), k5_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 10.80/4.68  tff(c_72, plain, (~r1_tarski(k4_xboole_0('#skF_3', '#skF_4'), k5_xboole_0('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_70])).
% 10.80/4.68  tff(c_657, plain, (k4_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), k5_xboole_0('#skF_4', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_649, c_72])).
% 10.80/4.68  tff(c_1370, plain, (k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', k5_xboole_0('#skF_4', '#skF_3')))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_657])).
% 10.80/4.68  tff(c_27411, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16159, c_1370])).
% 10.80/4.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.80/4.68  
% 10.80/4.68  Inference rules
% 10.80/4.68  ----------------------
% 10.80/4.68  #Ref     : 1
% 10.80/4.68  #Sup     : 7102
% 10.80/4.68  #Fact    : 0
% 10.80/4.68  #Define  : 0
% 10.80/4.68  #Split   : 2
% 10.80/4.68  #Chain   : 0
% 10.80/4.68  #Close   : 0
% 10.80/4.68  
% 10.80/4.68  Ordering : KBO
% 10.80/4.68  
% 10.80/4.68  Simplification rules
% 10.80/4.68  ----------------------
% 10.80/4.68  #Subsume      : 988
% 10.80/4.68  #Demod        : 5473
% 10.80/4.68  #Tautology    : 3773
% 10.80/4.68  #SimpNegUnit  : 9
% 10.80/4.68  #BackRed      : 5
% 10.80/4.68  
% 10.80/4.68  #Partial instantiations: 0
% 10.80/4.68  #Strategies tried      : 1
% 10.80/4.68  
% 10.80/4.68  Timing (in seconds)
% 10.80/4.68  ----------------------
% 10.80/4.68  Preprocessing        : 0.33
% 10.80/4.68  Parsing              : 0.18
% 10.80/4.68  CNF conversion       : 0.02
% 10.80/4.68  Main loop            : 3.56
% 10.80/4.68  Inferencing          : 0.69
% 10.80/4.68  Reduction            : 1.92
% 10.80/4.68  Demodulation         : 1.64
% 10.80/4.68  BG Simplification    : 0.09
% 10.80/4.68  Subsumption          : 0.67
% 10.80/4.68  Abstraction          : 0.12
% 10.80/4.68  MUC search           : 0.00
% 10.80/4.68  Cooper               : 0.00
% 10.80/4.68  Total                : 3.92
% 10.80/4.68  Index Insertion      : 0.00
% 10.80/4.68  Index Deletion       : 0.00
% 10.80/4.68  Index Matching       : 0.00
% 10.80/4.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
