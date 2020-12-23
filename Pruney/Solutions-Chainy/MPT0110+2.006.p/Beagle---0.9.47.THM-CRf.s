%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:08 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   26 (  28 expanded)
%              Number of leaves         :   16 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   19 (  21 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,k4_xboole_0(B,C))
     => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_xboole_1)).

tff(c_234,plain,(
    ! [A_39,B_40] : k4_xboole_0(k2_xboole_0(A_39,B_40),k3_xboole_0(A_39,B_40)) = k5_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_xboole_0(k4_xboole_0(A_6,B_7),B_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_378,plain,(
    ! [A_45,B_46] : r1_xboole_0(k5_xboole_0(A_45,B_46),k3_xboole_0(A_45,B_46)) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_8])).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_160,plain,(
    ! [B_32,A_33,C_34] :
      ( r1_xboole_0(B_32,k4_xboole_0(A_33,C_34))
      | ~ r1_xboole_0(A_33,k4_xboole_0(B_32,C_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_177,plain,(
    ! [A_3,A_33] :
      ( r1_xboole_0(A_3,k4_xboole_0(A_33,k1_xboole_0))
      | ~ r1_xboole_0(A_33,A_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_160])).

tff(c_182,plain,(
    ! [A_3,A_33] :
      ( r1_xboole_0(A_3,A_33)
      | ~ r1_xboole_0(A_33,A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_177])).

tff(c_393,plain,(
    ! [A_45,B_46] : r1_xboole_0(k3_xboole_0(A_45,B_46),k5_xboole_0(A_45,B_46)) ),
    inference(resolution,[status(thm)],[c_378,c_182])).

tff(c_18,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k5_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_899,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_393,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:04:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.38/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.35  
% 2.38/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.35  %$ r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 2.38/1.35  
% 2.38/1.35  %Foreground sorts:
% 2.38/1.35  
% 2.38/1.35  
% 2.38/1.35  %Background operators:
% 2.38/1.35  
% 2.38/1.35  
% 2.38/1.35  %Foreground operators:
% 2.38/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.38/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.38/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.38/1.35  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.38/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.38/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.38/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.38/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.38/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.38/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.38/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.38/1.35  
% 2.38/1.36  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l98_xboole_1)).
% 2.38/1.36  tff(f_33, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.38/1.36  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.38/1.36  tff(f_37, axiom, (![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_xboole_1)).
% 2.38/1.36  tff(f_46, negated_conjecture, ~(![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_xboole_1)).
% 2.38/1.36  tff(c_234, plain, (![A_39, B_40]: (k4_xboole_0(k2_xboole_0(A_39, B_40), k3_xboole_0(A_39, B_40))=k5_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.38/1.36  tff(c_8, plain, (![A_6, B_7]: (r1_xboole_0(k4_xboole_0(A_6, B_7), B_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.38/1.36  tff(c_378, plain, (![A_45, B_46]: (r1_xboole_0(k5_xboole_0(A_45, B_46), k3_xboole_0(A_45, B_46)))), inference(superposition, [status(thm), theory('equality')], [c_234, c_8])).
% 2.38/1.36  tff(c_4, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.38/1.36  tff(c_160, plain, (![B_32, A_33, C_34]: (r1_xboole_0(B_32, k4_xboole_0(A_33, C_34)) | ~r1_xboole_0(A_33, k4_xboole_0(B_32, C_34)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.38/1.36  tff(c_177, plain, (![A_3, A_33]: (r1_xboole_0(A_3, k4_xboole_0(A_33, k1_xboole_0)) | ~r1_xboole_0(A_33, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_160])).
% 2.38/1.36  tff(c_182, plain, (![A_3, A_33]: (r1_xboole_0(A_3, A_33) | ~r1_xboole_0(A_33, A_3))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_177])).
% 2.38/1.36  tff(c_393, plain, (![A_45, B_46]: (r1_xboole_0(k3_xboole_0(A_45, B_46), k5_xboole_0(A_45, B_46)))), inference(resolution, [status(thm)], [c_378, c_182])).
% 2.38/1.36  tff(c_18, plain, (~r1_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k5_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.38/1.36  tff(c_899, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_393, c_18])).
% 2.38/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.36  
% 2.38/1.36  Inference rules
% 2.38/1.36  ----------------------
% 2.38/1.36  #Ref     : 0
% 2.38/1.36  #Sup     : 217
% 2.38/1.36  #Fact    : 0
% 2.38/1.36  #Define  : 0
% 2.38/1.36  #Split   : 0
% 2.38/1.36  #Chain   : 0
% 2.38/1.36  #Close   : 0
% 2.38/1.36  
% 2.38/1.36  Ordering : KBO
% 2.38/1.36  
% 2.38/1.36  Simplification rules
% 2.38/1.36  ----------------------
% 2.38/1.36  #Subsume      : 1
% 2.38/1.36  #Demod        : 118
% 2.38/1.36  #Tautology    : 132
% 2.38/1.36  #SimpNegUnit  : 0
% 2.38/1.36  #BackRed      : 1
% 2.38/1.36  
% 2.38/1.36  #Partial instantiations: 0
% 2.38/1.36  #Strategies tried      : 1
% 2.38/1.36  
% 2.38/1.36  Timing (in seconds)
% 2.38/1.36  ----------------------
% 2.38/1.36  Preprocessing        : 0.29
% 2.38/1.36  Parsing              : 0.16
% 2.38/1.36  CNF conversion       : 0.02
% 2.38/1.36  Main loop            : 0.30
% 2.38/1.36  Inferencing          : 0.12
% 2.38/1.36  Reduction            : 0.10
% 2.38/1.36  Demodulation         : 0.07
% 2.38/1.36  BG Simplification    : 0.02
% 2.38/1.36  Subsumption          : 0.05
% 2.38/1.36  Abstraction          : 0.02
% 2.38/1.36  MUC search           : 0.00
% 2.38/1.36  Cooper               : 0.00
% 2.38/1.36  Total                : 0.60
% 2.38/1.36  Index Insertion      : 0.00
% 2.38/1.36  Index Deletion       : 0.00
% 2.38/1.36  Index Matching       : 0.00
% 2.38/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
