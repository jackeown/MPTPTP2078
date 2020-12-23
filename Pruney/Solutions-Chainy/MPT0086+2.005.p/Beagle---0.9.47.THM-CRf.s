%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:14 EST 2020

% Result     : Theorem 4.27s
% Output     : CNFRefutation 4.27s
% Verified   : 
% Statistics : Number of formulae       :   43 (  53 expanded)
%              Number of leaves         :   19 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :   38 (  48 expanded)
%              Number of equality atoms :   21 (  31 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_45,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_18,plain,(
    ! [A_16] : r1_xboole_0(A_16,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_73,plain,(
    ! [B_24,A_25] :
      ( r1_xboole_0(B_24,A_25)
      | ~ r1_xboole_0(A_25,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_76,plain,(
    ! [A_16] : r1_xboole_0(k1_xboole_0,A_16) ),
    inference(resolution,[status(thm)],[c_18,c_73])).

tff(c_8,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = k2_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_278,plain,(
    ! [A_39,B_40,C_41] : k4_xboole_0(k4_xboole_0(A_39,B_40),C_41) = k4_xboole_0(A_39,k2_xboole_0(B_40,C_41)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_94,plain,(
    ! [A_29,B_30] : k4_xboole_0(A_29,k4_xboole_0(A_29,B_30)) = k3_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_109,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k3_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_94])).

tff(c_112,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_109])).

tff(c_291,plain,(
    ! [A_39,B_40] : k4_xboole_0(A_39,k2_xboole_0(B_40,k4_xboole_0(A_39,B_40))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_278,c_112])).

tff(c_335,plain,(
    ! [A_39,B_40] : k4_xboole_0(A_39,k2_xboole_0(B_40,A_39)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_291])).

tff(c_287,plain,(
    ! [C_41,A_39,B_40] : k2_xboole_0(C_41,k4_xboole_0(A_39,k2_xboole_0(B_40,C_41))) = k2_xboole_0(C_41,k4_xboole_0(A_39,B_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_278,c_8])).

tff(c_12,plain,(
    ! [A_9,B_10,C_11] : k4_xboole_0(k4_xboole_0(A_9,B_10),C_11) = k4_xboole_0(A_9,k2_xboole_0(B_10,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_325,plain,(
    ! [A_39,B_40,B_13] : k4_xboole_0(A_39,k2_xboole_0(B_40,k4_xboole_0(k4_xboole_0(A_39,B_40),B_13))) = k3_xboole_0(k4_xboole_0(A_39,B_40),B_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_278])).

tff(c_4628,plain,(
    ! [A_117,B_118,B_119] : k4_xboole_0(A_117,k2_xboole_0(B_118,k4_xboole_0(A_117,k2_xboole_0(B_118,B_119)))) = k3_xboole_0(k4_xboole_0(A_117,B_118),B_119) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_325])).

tff(c_4779,plain,(
    ! [A_39,B_40] : k4_xboole_0(A_39,k2_xboole_0(B_40,k4_xboole_0(A_39,B_40))) = k3_xboole_0(k4_xboole_0(A_39,B_40),B_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_4628])).

tff(c_4927,plain,(
    ! [A_120,B_121] : k3_xboole_0(k4_xboole_0(A_120,B_121),B_121) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_8,c_4779])).

tff(c_20,plain,(
    ! [A_17,B_18] :
      ( ~ r1_xboole_0(k3_xboole_0(A_17,B_18),B_18)
      | r1_xboole_0(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4966,plain,(
    ! [B_121,A_120] :
      ( ~ r1_xboole_0(k1_xboole_0,B_121)
      | r1_xboole_0(k4_xboole_0(A_120,B_121),B_121) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4927,c_20])).

tff(c_5055,plain,(
    ! [A_120,B_121] : r1_xboole_0(k4_xboole_0(A_120,B_121),B_121) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_4966])).

tff(c_22,plain,(
    ~ r1_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_5078,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5055,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:26:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.27/1.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.27/1.82  
% 4.27/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.27/1.82  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 4.27/1.82  
% 4.27/1.82  %Foreground sorts:
% 4.27/1.82  
% 4.27/1.82  
% 4.27/1.82  %Background operators:
% 4.27/1.82  
% 4.27/1.82  
% 4.27/1.82  %Foreground operators:
% 4.27/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.27/1.82  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.27/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.27/1.82  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.27/1.82  tff('#skF_2', type, '#skF_2': $i).
% 4.27/1.82  tff('#skF_1', type, '#skF_1': $i).
% 4.27/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.27/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.27/1.82  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.27/1.82  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.27/1.82  
% 4.27/1.83  tff(f_45, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.27/1.83  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 4.27/1.83  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.27/1.83  tff(f_39, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.27/1.83  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 4.27/1.83  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.27/1.83  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.27/1.83  tff(f_51, axiom, (![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_xboole_1)).
% 4.27/1.83  tff(f_54, negated_conjecture, ~(![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 4.27/1.83  tff(c_18, plain, (![A_16]: (r1_xboole_0(A_16, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.27/1.83  tff(c_73, plain, (![B_24, A_25]: (r1_xboole_0(B_24, A_25) | ~r1_xboole_0(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.27/1.83  tff(c_76, plain, (![A_16]: (r1_xboole_0(k1_xboole_0, A_16))), inference(resolution, [status(thm)], [c_18, c_73])).
% 4.27/1.83  tff(c_8, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(B_7, A_6))=k2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.27/1.83  tff(c_278, plain, (![A_39, B_40, C_41]: (k4_xboole_0(k4_xboole_0(A_39, B_40), C_41)=k4_xboole_0(A_39, k2_xboole_0(B_40, C_41)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.27/1.83  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.27/1.83  tff(c_10, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.27/1.83  tff(c_94, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k4_xboole_0(A_29, B_30))=k3_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.27/1.83  tff(c_109, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k3_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_94])).
% 4.27/1.83  tff(c_112, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_109])).
% 4.27/1.83  tff(c_291, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k2_xboole_0(B_40, k4_xboole_0(A_39, B_40)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_278, c_112])).
% 4.27/1.83  tff(c_335, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k2_xboole_0(B_40, A_39))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_291])).
% 4.27/1.83  tff(c_287, plain, (![C_41, A_39, B_40]: (k2_xboole_0(C_41, k4_xboole_0(A_39, k2_xboole_0(B_40, C_41)))=k2_xboole_0(C_41, k4_xboole_0(A_39, B_40)))), inference(superposition, [status(thm), theory('equality')], [c_278, c_8])).
% 4.27/1.83  tff(c_12, plain, (![A_9, B_10, C_11]: (k4_xboole_0(k4_xboole_0(A_9, B_10), C_11)=k4_xboole_0(A_9, k2_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.27/1.83  tff(c_14, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.27/1.83  tff(c_325, plain, (![A_39, B_40, B_13]: (k4_xboole_0(A_39, k2_xboole_0(B_40, k4_xboole_0(k4_xboole_0(A_39, B_40), B_13)))=k3_xboole_0(k4_xboole_0(A_39, B_40), B_13))), inference(superposition, [status(thm), theory('equality')], [c_14, c_278])).
% 4.27/1.83  tff(c_4628, plain, (![A_117, B_118, B_119]: (k4_xboole_0(A_117, k2_xboole_0(B_118, k4_xboole_0(A_117, k2_xboole_0(B_118, B_119))))=k3_xboole_0(k4_xboole_0(A_117, B_118), B_119))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_325])).
% 4.27/1.83  tff(c_4779, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k2_xboole_0(B_40, k4_xboole_0(A_39, B_40)))=k3_xboole_0(k4_xboole_0(A_39, B_40), B_40))), inference(superposition, [status(thm), theory('equality')], [c_287, c_4628])).
% 4.27/1.83  tff(c_4927, plain, (![A_120, B_121]: (k3_xboole_0(k4_xboole_0(A_120, B_121), B_121)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_335, c_8, c_4779])).
% 4.27/1.83  tff(c_20, plain, (![A_17, B_18]: (~r1_xboole_0(k3_xboole_0(A_17, B_18), B_18) | r1_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.27/1.83  tff(c_4966, plain, (![B_121, A_120]: (~r1_xboole_0(k1_xboole_0, B_121) | r1_xboole_0(k4_xboole_0(A_120, B_121), B_121))), inference(superposition, [status(thm), theory('equality')], [c_4927, c_20])).
% 4.27/1.83  tff(c_5055, plain, (![A_120, B_121]: (r1_xboole_0(k4_xboole_0(A_120, B_121), B_121))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_4966])).
% 4.27/1.83  tff(c_22, plain, (~r1_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.27/1.83  tff(c_5078, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5055, c_22])).
% 4.27/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.27/1.83  
% 4.27/1.83  Inference rules
% 4.27/1.83  ----------------------
% 4.27/1.83  #Ref     : 0
% 4.27/1.83  #Sup     : 1264
% 4.27/1.83  #Fact    : 0
% 4.27/1.83  #Define  : 0
% 4.27/1.83  #Split   : 0
% 4.27/1.83  #Chain   : 0
% 4.27/1.83  #Close   : 0
% 4.27/1.83  
% 4.27/1.83  Ordering : KBO
% 4.27/1.83  
% 4.27/1.83  Simplification rules
% 4.27/1.83  ----------------------
% 4.27/1.83  #Subsume      : 3
% 4.27/1.83  #Demod        : 1421
% 4.27/1.83  #Tautology    : 880
% 4.27/1.83  #SimpNegUnit  : 0
% 4.27/1.83  #BackRed      : 1
% 4.27/1.83  
% 4.27/1.83  #Partial instantiations: 0
% 4.27/1.83  #Strategies tried      : 1
% 4.27/1.83  
% 4.27/1.83  Timing (in seconds)
% 4.27/1.83  ----------------------
% 4.27/1.83  Preprocessing        : 0.27
% 4.27/1.83  Parsing              : 0.15
% 4.27/1.83  CNF conversion       : 0.02
% 4.27/1.83  Main loop            : 0.80
% 4.27/1.83  Inferencing          : 0.25
% 4.27/1.83  Reduction            : 0.38
% 4.27/1.83  Demodulation         : 0.33
% 4.27/1.83  BG Simplification    : 0.03
% 4.27/1.83  Subsumption          : 0.09
% 4.27/1.83  Abstraction          : 0.04
% 4.27/1.83  MUC search           : 0.00
% 4.27/1.83  Cooper               : 0.00
% 4.27/1.83  Total                : 1.10
% 4.27/1.83  Index Insertion      : 0.00
% 4.27/1.83  Index Deletion       : 0.00
% 4.27/1.83  Index Matching       : 0.00
% 4.27/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
