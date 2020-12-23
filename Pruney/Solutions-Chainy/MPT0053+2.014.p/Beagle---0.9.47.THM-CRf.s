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
% DateTime   : Thu Dec  3 09:42:52 EST 2020

% Result     : Theorem 4.46s
% Output     : CNFRefutation 4.46s
% Verified   : 
% Statistics : Number of formulae       :   33 (  49 expanded)
%              Number of leaves         :   18 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   39 (  86 expanded)
%              Number of equality atoms :   14 (  27 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_47,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(c_38,plain,(
    ! [A_7,B_8,C_9] :
      ( r2_hidden('#skF_3'(A_7,B_8,C_9),A_7)
      | r2_hidden('#skF_4'(A_7,B_8,C_9),C_9)
      | k4_xboole_0(A_7,B_8) = C_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8,plain,(
    ! [D_6,A_1,B_2] :
      ( ~ r2_hidden(D_6,A_1)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_101,plain,(
    ! [A_38,B_39,C_40] :
      ( ~ r2_hidden('#skF_3'(A_38,B_39,C_40),B_39)
      | r2_hidden('#skF_4'(A_38,B_39,C_40),C_40)
      | k4_xboole_0(A_38,B_39) = C_40 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3201,plain,(
    ! [A_213,A_214,B_215,C_216] :
      ( r2_hidden('#skF_4'(A_213,k2_xboole_0(A_214,B_215),C_216),C_216)
      | k4_xboole_0(A_213,k2_xboole_0(A_214,B_215)) = C_216
      | ~ r2_hidden('#skF_3'(A_213,k2_xboole_0(A_214,B_215),C_216),A_214) ) ),
    inference(resolution,[status(thm)],[c_8,c_101])).

tff(c_3242,plain,(
    ! [A_217,B_218,C_219] :
      ( r2_hidden('#skF_4'(A_217,k2_xboole_0(A_217,B_218),C_219),C_219)
      | k4_xboole_0(A_217,k2_xboole_0(A_217,B_218)) = C_219 ) ),
    inference(resolution,[status(thm)],[c_38,c_3201])).

tff(c_40,plain,(
    ! [A_13] : k2_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_61,plain,(
    ! [D_21,B_22,A_23] :
      ( ~ r2_hidden(D_21,B_22)
      | r2_hidden(D_21,k2_xboole_0(A_23,B_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_64,plain,(
    ! [D_21,A_13] :
      ( ~ r2_hidden(D_21,k1_xboole_0)
      | r2_hidden(D_21,A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_61])).

tff(c_3291,plain,(
    ! [A_217,B_218,A_13] :
      ( r2_hidden('#skF_4'(A_217,k2_xboole_0(A_217,B_218),k1_xboole_0),A_13)
      | k4_xboole_0(A_217,k2_xboole_0(A_217,B_218)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_3242,c_64])).

tff(c_3298,plain,(
    ! [A_220,B_221,A_222] :
      ( r2_hidden('#skF_4'(A_220,k2_xboole_0(A_220,B_221),k1_xboole_0),A_222)
      | k4_xboole_0(A_220,k2_xboole_0(A_220,B_221)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_3242,c_64])).

tff(c_24,plain,(
    ! [D_12,B_8,A_7] :
      ( ~ r2_hidden(D_12,B_8)
      | ~ r2_hidden(D_12,k4_xboole_0(A_7,B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3355,plain,(
    ! [A_223,B_224,B_225] :
      ( ~ r2_hidden('#skF_4'(A_223,k2_xboole_0(A_223,B_224),k1_xboole_0),B_225)
      | k4_xboole_0(A_223,k2_xboole_0(A_223,B_224)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_3298,c_24])).

tff(c_3418,plain,(
    ! [A_217,B_218] : k4_xboole_0(A_217,k2_xboole_0(A_217,B_218)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3291,c_3355])).

tff(c_42,plain,(
    k4_xboole_0('#skF_5',k2_xboole_0('#skF_5','#skF_6')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3498,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3418,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:59:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.46/1.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.46/1.85  
% 4.46/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.46/1.85  %$ r2_hidden > k4_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 4.46/1.85  
% 4.46/1.85  %Foreground sorts:
% 4.46/1.85  
% 4.46/1.85  
% 4.46/1.85  %Background operators:
% 4.46/1.85  
% 4.46/1.85  
% 4.46/1.85  %Foreground operators:
% 4.46/1.85  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.46/1.85  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 4.46/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.46/1.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.46/1.85  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.46/1.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.46/1.85  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.46/1.85  tff('#skF_5', type, '#skF_5': $i).
% 4.46/1.85  tff('#skF_6', type, '#skF_6': $i).
% 4.46/1.85  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.46/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.46/1.85  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.46/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.46/1.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.46/1.85  
% 4.46/1.86  tff(f_45, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.46/1.86  tff(f_35, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 4.46/1.86  tff(f_47, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 4.46/1.86  tff(f_50, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 4.46/1.86  tff(c_38, plain, (![A_7, B_8, C_9]: (r2_hidden('#skF_3'(A_7, B_8, C_9), A_7) | r2_hidden('#skF_4'(A_7, B_8, C_9), C_9) | k4_xboole_0(A_7, B_8)=C_9)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.46/1.86  tff(c_8, plain, (![D_6, A_1, B_2]: (~r2_hidden(D_6, A_1) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.46/1.86  tff(c_101, plain, (![A_38, B_39, C_40]: (~r2_hidden('#skF_3'(A_38, B_39, C_40), B_39) | r2_hidden('#skF_4'(A_38, B_39, C_40), C_40) | k4_xboole_0(A_38, B_39)=C_40)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.46/1.86  tff(c_3201, plain, (![A_213, A_214, B_215, C_216]: (r2_hidden('#skF_4'(A_213, k2_xboole_0(A_214, B_215), C_216), C_216) | k4_xboole_0(A_213, k2_xboole_0(A_214, B_215))=C_216 | ~r2_hidden('#skF_3'(A_213, k2_xboole_0(A_214, B_215), C_216), A_214))), inference(resolution, [status(thm)], [c_8, c_101])).
% 4.46/1.86  tff(c_3242, plain, (![A_217, B_218, C_219]: (r2_hidden('#skF_4'(A_217, k2_xboole_0(A_217, B_218), C_219), C_219) | k4_xboole_0(A_217, k2_xboole_0(A_217, B_218))=C_219)), inference(resolution, [status(thm)], [c_38, c_3201])).
% 4.46/1.86  tff(c_40, plain, (![A_13]: (k2_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.46/1.86  tff(c_61, plain, (![D_21, B_22, A_23]: (~r2_hidden(D_21, B_22) | r2_hidden(D_21, k2_xboole_0(A_23, B_22)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.46/1.86  tff(c_64, plain, (![D_21, A_13]: (~r2_hidden(D_21, k1_xboole_0) | r2_hidden(D_21, A_13))), inference(superposition, [status(thm), theory('equality')], [c_40, c_61])).
% 4.46/1.86  tff(c_3291, plain, (![A_217, B_218, A_13]: (r2_hidden('#skF_4'(A_217, k2_xboole_0(A_217, B_218), k1_xboole_0), A_13) | k4_xboole_0(A_217, k2_xboole_0(A_217, B_218))=k1_xboole_0)), inference(resolution, [status(thm)], [c_3242, c_64])).
% 4.46/1.86  tff(c_3298, plain, (![A_220, B_221, A_222]: (r2_hidden('#skF_4'(A_220, k2_xboole_0(A_220, B_221), k1_xboole_0), A_222) | k4_xboole_0(A_220, k2_xboole_0(A_220, B_221))=k1_xboole_0)), inference(resolution, [status(thm)], [c_3242, c_64])).
% 4.46/1.86  tff(c_24, plain, (![D_12, B_8, A_7]: (~r2_hidden(D_12, B_8) | ~r2_hidden(D_12, k4_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.46/1.86  tff(c_3355, plain, (![A_223, B_224, B_225]: (~r2_hidden('#skF_4'(A_223, k2_xboole_0(A_223, B_224), k1_xboole_0), B_225) | k4_xboole_0(A_223, k2_xboole_0(A_223, B_224))=k1_xboole_0)), inference(resolution, [status(thm)], [c_3298, c_24])).
% 4.46/1.86  tff(c_3418, plain, (![A_217, B_218]: (k4_xboole_0(A_217, k2_xboole_0(A_217, B_218))=k1_xboole_0)), inference(resolution, [status(thm)], [c_3291, c_3355])).
% 4.46/1.86  tff(c_42, plain, (k4_xboole_0('#skF_5', k2_xboole_0('#skF_5', '#skF_6'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.46/1.86  tff(c_3498, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3418, c_42])).
% 4.46/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.46/1.86  
% 4.46/1.86  Inference rules
% 4.46/1.86  ----------------------
% 4.46/1.86  #Ref     : 0
% 4.46/1.86  #Sup     : 705
% 4.46/1.86  #Fact    : 6
% 4.46/1.86  #Define  : 0
% 4.46/1.86  #Split   : 0
% 4.46/1.86  #Chain   : 0
% 4.46/1.86  #Close   : 0
% 4.46/1.86  
% 4.46/1.86  Ordering : KBO
% 4.46/1.86  
% 4.46/1.86  Simplification rules
% 4.46/1.86  ----------------------
% 4.46/1.86  #Subsume      : 161
% 4.46/1.86  #Demod        : 385
% 4.46/1.86  #Tautology    : 251
% 4.46/1.86  #SimpNegUnit  : 0
% 4.46/1.86  #BackRed      : 6
% 4.46/1.86  
% 4.46/1.86  #Partial instantiations: 0
% 4.46/1.86  #Strategies tried      : 1
% 4.46/1.86  
% 4.46/1.86  Timing (in seconds)
% 4.46/1.86  ----------------------
% 4.46/1.86  Preprocessing        : 0.29
% 4.46/1.86  Parsing              : 0.14
% 4.46/1.86  CNF conversion       : 0.02
% 4.46/1.86  Main loop            : 0.74
% 4.46/1.86  Inferencing          : 0.29
% 4.46/1.86  Reduction            : 0.19
% 4.46/1.86  Demodulation         : 0.13
% 4.46/1.86  BG Simplification    : 0.04
% 4.46/1.86  Subsumption          : 0.16
% 4.46/1.87  Abstraction          : 0.05
% 4.46/1.87  MUC search           : 0.00
% 4.46/1.87  Cooper               : 0.00
% 4.46/1.87  Total                : 1.06
% 4.46/1.87  Index Insertion      : 0.00
% 4.46/1.87  Index Deletion       : 0.00
% 4.46/1.87  Index Matching       : 0.00
% 4.46/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
