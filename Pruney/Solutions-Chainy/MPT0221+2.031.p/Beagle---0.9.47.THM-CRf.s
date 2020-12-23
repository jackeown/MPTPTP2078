%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:15 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 109 expanded)
%              Number of leaves         :   22 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :   54 ( 161 expanded)
%              Number of equality atoms :   15 (  60 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
          & A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_57,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
     => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l20_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_30,plain,(
    '#skF_2' = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_32,plain,(
    r1_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_33,plain,(
    r1_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32])).

tff(c_12,plain,(
    ! [A_7] :
      ( ~ r1_xboole_0(A_7,A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_51,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_33,c_12])).

tff(c_26,plain,(
    ! [B_16] : r1_tarski(k1_tarski(B_16),k1_tarski(B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_61,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_26])).

tff(c_67,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_61])).

tff(c_8,plain,(
    ! [A_6] : r1_xboole_0(A_6,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_191,plain,(
    ! [A_43,B_44] :
      ( k4_xboole_0(k2_xboole_0(A_43,B_44),B_44) = A_43
      | ~ r1_xboole_0(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_70,plain,(
    ! [A_21,B_22] :
      ( k4_xboole_0(A_21,B_22) = A_21
      | ~ r1_xboole_0(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_74,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(resolution,[status(thm)],[c_8,c_70])).

tff(c_198,plain,(
    ! [A_43] :
      ( k2_xboole_0(A_43,k1_xboole_0) = A_43
      | ~ r1_xboole_0(A_43,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_74])).

tff(c_208,plain,(
    ! [A_43] : k2_xboole_0(A_43,k1_xboole_0) = A_43 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_198])).

tff(c_226,plain,(
    ! [A_46,B_47] :
      ( r2_hidden(A_46,B_47)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(A_46),B_47),B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_235,plain,(
    ! [A_48] :
      ( r2_hidden(A_48,k1_xboole_0)
      | ~ r1_tarski(k1_tarski(A_48),k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_226])).

tff(c_238,plain,
    ( r2_hidden('#skF_3',k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_235])).

tff(c_240,plain,(
    r2_hidden('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_238])).

tff(c_103,plain,(
    ! [A_31,B_32,C_33] :
      ( ~ r1_xboole_0(A_31,B_32)
      | ~ r2_hidden(C_33,B_32)
      | ~ r2_hidden(C_33,A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_109,plain,(
    ! [C_33,A_6] :
      ( ~ r2_hidden(C_33,k1_xboole_0)
      | ~ r2_hidden(C_33,A_6) ) ),
    inference(resolution,[status(thm)],[c_8,c_103])).

tff(c_243,plain,(
    ! [A_6] : ~ r2_hidden('#skF_3',A_6) ),
    inference(resolution,[status(thm)],[c_240,c_109])).

tff(c_253,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_243,c_240])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:05:20 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.26  
% 2.14/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.26  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.14/1.26  
% 2.14/1.26  %Foreground sorts:
% 2.14/1.26  
% 2.14/1.26  
% 2.14/1.26  %Background operators:
% 2.14/1.26  
% 2.14/1.26  
% 2.14/1.26  %Foreground operators:
% 2.14/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.14/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.14/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.14/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.14/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.14/1.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.14/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.14/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.14/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.14/1.26  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.14/1.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.14/1.26  
% 2.14/1.27  tff(f_83, negated_conjecture, ~(![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 2.14/1.27  tff(f_57, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.14/1.27  tff(f_77, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.14/1.27  tff(f_45, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.14/1.27  tff(f_65, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_xboole_1)).
% 2.14/1.27  tff(f_61, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.14/1.27  tff(f_71, axiom, (![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l20_zfmisc_1)).
% 2.14/1.27  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.14/1.27  tff(c_30, plain, ('#skF_2'='#skF_3'), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.14/1.27  tff(c_32, plain, (r1_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.14/1.27  tff(c_33, plain, (r1_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32])).
% 2.14/1.27  tff(c_12, plain, (![A_7]: (~r1_xboole_0(A_7, A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.14/1.27  tff(c_51, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_33, c_12])).
% 2.14/1.27  tff(c_26, plain, (![B_16]: (r1_tarski(k1_tarski(B_16), k1_tarski(B_16)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.14/1.27  tff(c_61, plain, (r1_tarski(k1_tarski('#skF_3'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_51, c_26])).
% 2.14/1.27  tff(c_67, plain, (r1_tarski(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_51, c_61])).
% 2.14/1.27  tff(c_8, plain, (![A_6]: (r1_xboole_0(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.14/1.27  tff(c_191, plain, (![A_43, B_44]: (k4_xboole_0(k2_xboole_0(A_43, B_44), B_44)=A_43 | ~r1_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.14/1.27  tff(c_70, plain, (![A_21, B_22]: (k4_xboole_0(A_21, B_22)=A_21 | ~r1_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.14/1.27  tff(c_74, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(resolution, [status(thm)], [c_8, c_70])).
% 2.14/1.27  tff(c_198, plain, (![A_43]: (k2_xboole_0(A_43, k1_xboole_0)=A_43 | ~r1_xboole_0(A_43, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_191, c_74])).
% 2.14/1.27  tff(c_208, plain, (![A_43]: (k2_xboole_0(A_43, k1_xboole_0)=A_43)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_198])).
% 2.14/1.27  tff(c_226, plain, (![A_46, B_47]: (r2_hidden(A_46, B_47) | ~r1_tarski(k2_xboole_0(k1_tarski(A_46), B_47), B_47))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.14/1.27  tff(c_235, plain, (![A_48]: (r2_hidden(A_48, k1_xboole_0) | ~r1_tarski(k1_tarski(A_48), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_208, c_226])).
% 2.14/1.27  tff(c_238, plain, (r2_hidden('#skF_3', k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_51, c_235])).
% 2.14/1.27  tff(c_240, plain, (r2_hidden('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_67, c_238])).
% 2.14/1.27  tff(c_103, plain, (![A_31, B_32, C_33]: (~r1_xboole_0(A_31, B_32) | ~r2_hidden(C_33, B_32) | ~r2_hidden(C_33, A_31))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.14/1.27  tff(c_109, plain, (![C_33, A_6]: (~r2_hidden(C_33, k1_xboole_0) | ~r2_hidden(C_33, A_6))), inference(resolution, [status(thm)], [c_8, c_103])).
% 2.14/1.27  tff(c_243, plain, (![A_6]: (~r2_hidden('#skF_3', A_6))), inference(resolution, [status(thm)], [c_240, c_109])).
% 2.14/1.27  tff(c_253, plain, $false, inference(negUnitSimplification, [status(thm)], [c_243, c_240])).
% 2.14/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.27  
% 2.14/1.27  Inference rules
% 2.14/1.27  ----------------------
% 2.14/1.27  #Ref     : 0
% 2.14/1.27  #Sup     : 45
% 2.14/1.27  #Fact    : 0
% 2.14/1.27  #Define  : 0
% 2.14/1.27  #Split   : 0
% 2.14/1.27  #Chain   : 0
% 2.14/1.27  #Close   : 0
% 2.14/1.27  
% 2.14/1.27  Ordering : KBO
% 2.14/1.27  
% 2.14/1.27  Simplification rules
% 2.14/1.27  ----------------------
% 2.14/1.27  #Subsume      : 1
% 2.14/1.27  #Demod        : 20
% 2.14/1.27  #Tautology    : 32
% 2.14/1.27  #SimpNegUnit  : 2
% 2.14/1.27  #BackRed      : 3
% 2.14/1.27  
% 2.14/1.27  #Partial instantiations: 0
% 2.14/1.27  #Strategies tried      : 1
% 2.14/1.27  
% 2.14/1.27  Timing (in seconds)
% 2.14/1.27  ----------------------
% 2.14/1.27  Preprocessing        : 0.32
% 2.14/1.27  Parsing              : 0.17
% 2.14/1.27  CNF conversion       : 0.02
% 2.14/1.27  Main loop            : 0.16
% 2.14/1.27  Inferencing          : 0.06
% 2.14/1.27  Reduction            : 0.05
% 2.14/1.27  Demodulation         : 0.04
% 2.14/1.27  BG Simplification    : 0.01
% 2.14/1.28  Subsumption          : 0.03
% 2.14/1.28  Abstraction          : 0.01
% 2.14/1.28  MUC search           : 0.00
% 2.14/1.28  Cooper               : 0.00
% 2.14/1.28  Total                : 0.51
% 2.14/1.28  Index Insertion      : 0.00
% 2.14/1.28  Index Deletion       : 0.00
% 2.14/1.28  Index Matching       : 0.00
% 2.14/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
