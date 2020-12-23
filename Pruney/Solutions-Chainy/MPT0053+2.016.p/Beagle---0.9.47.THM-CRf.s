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
% DateTime   : Thu Dec  3 09:42:52 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   29 (  37 expanded)
%              Number of leaves         :   15 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   30 (  54 expanded)
%              Number of equality atoms :   15 (  23 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(c_22,plain,(
    ! [A_10] : k4_xboole_0(k1_xboole_0,A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_265,plain,(
    ! [A_57,B_58,C_59] :
      ( ~ r2_hidden('#skF_1'(A_57,B_58,C_59),B_58)
      | r2_hidden('#skF_2'(A_57,B_58,C_59),C_59)
      | k4_xboole_0(A_57,B_58) = C_59 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_280,plain,(
    ! [A_1,C_3] :
      ( r2_hidden('#skF_2'(A_1,A_1,C_3),C_3)
      | k4_xboole_0(A_1,A_1) = C_3 ) ),
    inference(resolution,[status(thm)],[c_18,c_265])).

tff(c_282,plain,(
    ! [A_60,C_61] :
      ( r2_hidden('#skF_2'(A_60,A_60,C_61),C_61)
      | k4_xboole_0(A_60,A_60) = C_61 ) ),
    inference(resolution,[status(thm)],[c_18,c_265])).

tff(c_36,plain,(
    ! [D_15,B_16,A_17] :
      ( ~ r2_hidden(D_15,B_16)
      | ~ r2_hidden(D_15,k4_xboole_0(A_17,B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_39,plain,(
    ! [D_15,A_10] :
      ( ~ r2_hidden(D_15,A_10)
      | ~ r2_hidden(D_15,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_36])).

tff(c_321,plain,(
    ! [A_62,C_63] :
      ( ~ r2_hidden('#skF_2'(A_62,A_62,C_63),k1_xboole_0)
      | k4_xboole_0(A_62,A_62) = C_63 ) ),
    inference(resolution,[status(thm)],[c_282,c_39])).

tff(c_331,plain,(
    ! [A_64] : k4_xboole_0(A_64,A_64) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_280,c_321])).

tff(c_20,plain,(
    ! [A_7,B_8,C_9] : k4_xboole_0(k4_xboole_0(A_7,B_8),C_9) = k4_xboole_0(A_7,k2_xboole_0(B_8,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_352,plain,(
    ! [A_64,C_9] : k4_xboole_0(A_64,k2_xboole_0(A_64,C_9)) = k4_xboole_0(k1_xboole_0,C_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_20])).

tff(c_376,plain,(
    ! [A_64,C_9] : k4_xboole_0(A_64,k2_xboole_0(A_64,C_9)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_352])).

tff(c_24,plain,(
    k4_xboole_0('#skF_3',k2_xboole_0('#skF_3','#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_410,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:14:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.28  
% 2.03/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.28  %$ r2_hidden > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.03/1.28  
% 2.03/1.28  %Foreground sorts:
% 2.03/1.28  
% 2.03/1.28  
% 2.03/1.28  %Background operators:
% 2.03/1.28  
% 2.03/1.28  
% 2.03/1.28  %Foreground operators:
% 2.03/1.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.03/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.03/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.03/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.03/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.03/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.03/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.03/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.03/1.28  
% 2.03/1.29  tff(f_39, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.03/1.29  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.03/1.29  tff(f_37, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 2.03/1.29  tff(f_42, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.03/1.29  tff(c_22, plain, (![A_10]: (k4_xboole_0(k1_xboole_0, A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.03/1.29  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.03/1.29  tff(c_265, plain, (![A_57, B_58, C_59]: (~r2_hidden('#skF_1'(A_57, B_58, C_59), B_58) | r2_hidden('#skF_2'(A_57, B_58, C_59), C_59) | k4_xboole_0(A_57, B_58)=C_59)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.03/1.29  tff(c_280, plain, (![A_1, C_3]: (r2_hidden('#skF_2'(A_1, A_1, C_3), C_3) | k4_xboole_0(A_1, A_1)=C_3)), inference(resolution, [status(thm)], [c_18, c_265])).
% 2.03/1.29  tff(c_282, plain, (![A_60, C_61]: (r2_hidden('#skF_2'(A_60, A_60, C_61), C_61) | k4_xboole_0(A_60, A_60)=C_61)), inference(resolution, [status(thm)], [c_18, c_265])).
% 2.03/1.29  tff(c_36, plain, (![D_15, B_16, A_17]: (~r2_hidden(D_15, B_16) | ~r2_hidden(D_15, k4_xboole_0(A_17, B_16)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.03/1.29  tff(c_39, plain, (![D_15, A_10]: (~r2_hidden(D_15, A_10) | ~r2_hidden(D_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_36])).
% 2.03/1.29  tff(c_321, plain, (![A_62, C_63]: (~r2_hidden('#skF_2'(A_62, A_62, C_63), k1_xboole_0) | k4_xboole_0(A_62, A_62)=C_63)), inference(resolution, [status(thm)], [c_282, c_39])).
% 2.03/1.29  tff(c_331, plain, (![A_64]: (k4_xboole_0(A_64, A_64)=k1_xboole_0)), inference(resolution, [status(thm)], [c_280, c_321])).
% 2.03/1.29  tff(c_20, plain, (![A_7, B_8, C_9]: (k4_xboole_0(k4_xboole_0(A_7, B_8), C_9)=k4_xboole_0(A_7, k2_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.03/1.29  tff(c_352, plain, (![A_64, C_9]: (k4_xboole_0(A_64, k2_xboole_0(A_64, C_9))=k4_xboole_0(k1_xboole_0, C_9))), inference(superposition, [status(thm), theory('equality')], [c_331, c_20])).
% 2.03/1.29  tff(c_376, plain, (![A_64, C_9]: (k4_xboole_0(A_64, k2_xboole_0(A_64, C_9))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_352])).
% 2.03/1.29  tff(c_24, plain, (k4_xboole_0('#skF_3', k2_xboole_0('#skF_3', '#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.03/1.29  tff(c_410, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_376, c_24])).
% 2.03/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.29  
% 2.03/1.29  Inference rules
% 2.03/1.29  ----------------------
% 2.03/1.29  #Ref     : 0
% 2.03/1.29  #Sup     : 90
% 2.03/1.29  #Fact    : 0
% 2.03/1.29  #Define  : 0
% 2.03/1.29  #Split   : 0
% 2.03/1.29  #Chain   : 0
% 2.03/1.29  #Close   : 0
% 2.03/1.29  
% 2.03/1.29  Ordering : KBO
% 2.03/1.29  
% 2.03/1.29  Simplification rules
% 2.03/1.29  ----------------------
% 2.03/1.29  #Subsume      : 14
% 2.03/1.29  #Demod        : 19
% 2.03/1.29  #Tautology    : 17
% 2.03/1.29  #SimpNegUnit  : 0
% 2.03/1.29  #BackRed      : 3
% 2.03/1.29  
% 2.03/1.29  #Partial instantiations: 0
% 2.03/1.29  #Strategies tried      : 1
% 2.03/1.29  
% 2.03/1.29  Timing (in seconds)
% 2.03/1.29  ----------------------
% 2.03/1.29  Preprocessing        : 0.27
% 2.03/1.29  Parsing              : 0.15
% 2.03/1.29  CNF conversion       : 0.02
% 2.03/1.29  Main loop            : 0.23
% 2.03/1.29  Inferencing          : 0.09
% 2.03/1.29  Reduction            : 0.06
% 2.03/1.29  Demodulation         : 0.04
% 2.03/1.29  BG Simplification    : 0.01
% 2.03/1.29  Subsumption          : 0.05
% 2.03/1.29  Abstraction          : 0.01
% 2.03/1.29  MUC search           : 0.00
% 2.03/1.29  Cooper               : 0.00
% 2.03/1.29  Total                : 0.52
% 2.03/1.29  Index Insertion      : 0.00
% 2.03/1.29  Index Deletion       : 0.00
% 2.03/1.29  Index Matching       : 0.00
% 2.03/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
