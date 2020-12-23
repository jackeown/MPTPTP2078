%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:09 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   47 (  64 expanded)
%              Number of leaves         :   23 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   60 ( 103 expanded)
%              Number of equality atoms :   12 (  19 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( A != k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ! [D] :
                  ( r2_hidden(D,A)
                 => r2_hidden(C,D) ) ) ) )
      & ( A = k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

tff(f_44,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_48,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_52,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_9'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_87,plain,(
    ! [A_43,B_44] :
      ( r2_hidden('#skF_1'(A_43,B_44),A_43)
      | r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_96,plain,(
    ! [A_43] : r1_tarski(A_43,A_43) ),
    inference(resolution,[status(thm)],[c_87,c_4])).

tff(c_54,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_246,plain,(
    ! [C_73,D_74,A_75] :
      ( r2_hidden(C_73,D_74)
      | ~ r2_hidden(D_74,A_75)
      | ~ r2_hidden(C_73,k1_setfam_1(A_75))
      | k1_xboole_0 = A_75 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_261,plain,(
    ! [C_73] :
      ( r2_hidden(C_73,'#skF_8')
      | ~ r2_hidden(C_73,k1_setfam_1('#skF_9'))
      | k1_xboole_0 = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_54,c_246])).

tff(c_278,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_261])).

tff(c_128,plain,(
    ! [C_53,B_54,A_55] :
      ( r2_hidden(C_53,B_54)
      | ~ r2_hidden(C_53,A_55)
      | ~ r1_tarski(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_142,plain,(
    ! [B_57] :
      ( r2_hidden('#skF_8',B_57)
      | ~ r1_tarski('#skF_9',B_57) ) ),
    inference(resolution,[status(thm)],[c_54,c_128])).

tff(c_61,plain,(
    ! [A_35,B_36] : r1_tarski(k4_xboole_0(A_35,B_36),A_35) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_28,plain,(
    ! [A_14] :
      ( k1_xboole_0 = A_14
      | ~ r1_tarski(A_14,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_66,plain,(
    ! [B_36] : k4_xboole_0(k1_xboole_0,B_36) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_61,c_28])).

tff(c_106,plain,(
    ! [D_46,B_47,A_48] :
      ( ~ r2_hidden(D_46,B_47)
      | ~ r2_hidden(D_46,k4_xboole_0(A_48,B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_115,plain,(
    ! [D_49,B_50] :
      ( ~ r2_hidden(D_49,B_50)
      | ~ r2_hidden(D_49,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_106])).

tff(c_121,plain,(
    ~ r2_hidden('#skF_8',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_54,c_115])).

tff(c_159,plain,(
    ~ r1_tarski('#skF_9',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_142,c_121])).

tff(c_282,plain,(
    ~ r1_tarski('#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_159])).

tff(c_292,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_282])).

tff(c_295,plain,(
    ! [C_78] :
      ( r2_hidden(C_78,'#skF_8')
      | ~ r2_hidden(C_78,k1_setfam_1('#skF_9')) ) ),
    inference(splitRight,[status(thm)],[c_261])).

tff(c_312,plain,(
    ! [B_79] :
      ( r2_hidden('#skF_1'(k1_setfam_1('#skF_9'),B_79),'#skF_8')
      | r1_tarski(k1_setfam_1('#skF_9'),B_79) ) ),
    inference(resolution,[status(thm)],[c_6,c_295])).

tff(c_322,plain,(
    r1_tarski(k1_setfam_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_312,c_4])).

tff(c_329,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_52,c_322])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:39:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.27  
% 2.19/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.28  %$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7 > #skF_1 > #skF_5
% 2.19/1.28  
% 2.19/1.28  %Foreground sorts:
% 2.19/1.28  
% 2.19/1.28  
% 2.19/1.28  %Background operators:
% 2.19/1.28  
% 2.19/1.28  
% 2.19/1.28  %Foreground operators:
% 2.19/1.28  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.19/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.19/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.19/1.28  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.19/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.19/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.19/1.28  tff('#skF_9', type, '#skF_9': $i).
% 2.19/1.28  tff('#skF_8', type, '#skF_8': $i).
% 2.19/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.28  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.19/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.28  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.19/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.19/1.28  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.19/1.28  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.19/1.28  
% 2.19/1.29  tff(f_72, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 2.19/1.29  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.19/1.29  tff(f_67, axiom, (![A, B]: ((~(A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (![D]: (r2_hidden(D, A) => r2_hidden(C, D))))))) & ((A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (B = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_setfam_1)).
% 2.19/1.29  tff(f_44, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.19/1.29  tff(f_48, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.19/1.29  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.19/1.29  tff(c_52, plain, (~r1_tarski(k1_setfam_1('#skF_9'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.19/1.29  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.19/1.29  tff(c_87, plain, (![A_43, B_44]: (r2_hidden('#skF_1'(A_43, B_44), A_43) | r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.19/1.29  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.19/1.29  tff(c_96, plain, (![A_43]: (r1_tarski(A_43, A_43))), inference(resolution, [status(thm)], [c_87, c_4])).
% 2.19/1.29  tff(c_54, plain, (r2_hidden('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.19/1.29  tff(c_246, plain, (![C_73, D_74, A_75]: (r2_hidden(C_73, D_74) | ~r2_hidden(D_74, A_75) | ~r2_hidden(C_73, k1_setfam_1(A_75)) | k1_xboole_0=A_75)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.19/1.29  tff(c_261, plain, (![C_73]: (r2_hidden(C_73, '#skF_8') | ~r2_hidden(C_73, k1_setfam_1('#skF_9')) | k1_xboole_0='#skF_9')), inference(resolution, [status(thm)], [c_54, c_246])).
% 2.19/1.29  tff(c_278, plain, (k1_xboole_0='#skF_9'), inference(splitLeft, [status(thm)], [c_261])).
% 2.19/1.29  tff(c_128, plain, (![C_53, B_54, A_55]: (r2_hidden(C_53, B_54) | ~r2_hidden(C_53, A_55) | ~r1_tarski(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.19/1.29  tff(c_142, plain, (![B_57]: (r2_hidden('#skF_8', B_57) | ~r1_tarski('#skF_9', B_57))), inference(resolution, [status(thm)], [c_54, c_128])).
% 2.19/1.29  tff(c_61, plain, (![A_35, B_36]: (r1_tarski(k4_xboole_0(A_35, B_36), A_35))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.19/1.29  tff(c_28, plain, (![A_14]: (k1_xboole_0=A_14 | ~r1_tarski(A_14, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.19/1.29  tff(c_66, plain, (![B_36]: (k4_xboole_0(k1_xboole_0, B_36)=k1_xboole_0)), inference(resolution, [status(thm)], [c_61, c_28])).
% 2.19/1.29  tff(c_106, plain, (![D_46, B_47, A_48]: (~r2_hidden(D_46, B_47) | ~r2_hidden(D_46, k4_xboole_0(A_48, B_47)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.19/1.29  tff(c_115, plain, (![D_49, B_50]: (~r2_hidden(D_49, B_50) | ~r2_hidden(D_49, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_66, c_106])).
% 2.19/1.29  tff(c_121, plain, (~r2_hidden('#skF_8', k1_xboole_0)), inference(resolution, [status(thm)], [c_54, c_115])).
% 2.19/1.29  tff(c_159, plain, (~r1_tarski('#skF_9', k1_xboole_0)), inference(resolution, [status(thm)], [c_142, c_121])).
% 2.19/1.29  tff(c_282, plain, (~r1_tarski('#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_278, c_159])).
% 2.19/1.29  tff(c_292, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_282])).
% 2.19/1.29  tff(c_295, plain, (![C_78]: (r2_hidden(C_78, '#skF_8') | ~r2_hidden(C_78, k1_setfam_1('#skF_9')))), inference(splitRight, [status(thm)], [c_261])).
% 2.19/1.29  tff(c_312, plain, (![B_79]: (r2_hidden('#skF_1'(k1_setfam_1('#skF_9'), B_79), '#skF_8') | r1_tarski(k1_setfam_1('#skF_9'), B_79))), inference(resolution, [status(thm)], [c_6, c_295])).
% 2.19/1.29  tff(c_322, plain, (r1_tarski(k1_setfam_1('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_312, c_4])).
% 2.19/1.29  tff(c_329, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_52, c_322])).
% 2.19/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.29  
% 2.19/1.29  Inference rules
% 2.19/1.29  ----------------------
% 2.19/1.29  #Ref     : 0
% 2.19/1.29  #Sup     : 59
% 2.19/1.29  #Fact    : 0
% 2.19/1.29  #Define  : 0
% 2.19/1.29  #Split   : 2
% 2.19/1.29  #Chain   : 0
% 2.19/1.29  #Close   : 0
% 2.19/1.29  
% 2.19/1.29  Ordering : KBO
% 2.19/1.29  
% 2.19/1.29  Simplification rules
% 2.19/1.29  ----------------------
% 2.19/1.29  #Subsume      : 9
% 2.19/1.29  #Demod        : 22
% 2.19/1.29  #Tautology    : 18
% 2.19/1.29  #SimpNegUnit  : 2
% 2.19/1.29  #BackRed      : 11
% 2.19/1.29  
% 2.19/1.29  #Partial instantiations: 0
% 2.19/1.29  #Strategies tried      : 1
% 2.19/1.29  
% 2.19/1.29  Timing (in seconds)
% 2.19/1.29  ----------------------
% 2.19/1.29  Preprocessing        : 0.29
% 2.19/1.29  Parsing              : 0.15
% 2.19/1.29  CNF conversion       : 0.03
% 2.19/1.29  Main loop            : 0.22
% 2.19/1.29  Inferencing          : 0.07
% 2.19/1.29  Reduction            : 0.06
% 2.19/1.29  Demodulation         : 0.04
% 2.19/1.29  BG Simplification    : 0.02
% 2.19/1.29  Subsumption          : 0.06
% 2.19/1.29  Abstraction          : 0.01
% 2.19/1.29  MUC search           : 0.00
% 2.19/1.29  Cooper               : 0.00
% 2.19/1.29  Total                : 0.54
% 2.19/1.29  Index Insertion      : 0.00
% 2.19/1.29  Index Deletion       : 0.00
% 2.19/1.29  Index Matching       : 0.00
% 2.19/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
