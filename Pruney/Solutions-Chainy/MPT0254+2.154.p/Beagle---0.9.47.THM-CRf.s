%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:38 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   36 (  71 expanded)
%              Number of leaves         :   19 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   45 (  92 expanded)
%              Number of equality atoms :    8 (  44 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_66,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_96,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( k2_xboole_0(A,B) = k1_xboole_0
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_xboole_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
     => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l20_zfmisc_1)).

tff(f_68,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_18,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_32,plain,(
    k2_xboole_0(k1_tarski('#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_39,plain,(
    ! [A_22,B_23] :
      ( k1_xboole_0 = A_22
      | k2_xboole_0(A_22,B_23) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_43,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_39])).

tff(c_44,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_32])).

tff(c_105,plain,(
    ! [A_40,B_41] :
      ( r2_hidden(A_40,B_41)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(A_40),B_41),B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_150,plain,(
    ! [B_51] :
      ( r2_hidden('#skF_2',B_51)
      | ~ r1_tarski(k2_xboole_0(k1_xboole_0,B_51),B_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_105])).

tff(c_153,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_150])).

tff(c_155,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_153])).

tff(c_20,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_74,plain,(
    ! [A_27,C_28,B_29] :
      ( r1_xboole_0(A_27,C_28)
      | ~ r1_xboole_0(A_27,k2_xboole_0(B_29,C_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_77,plain,(
    ! [A_27] :
      ( r1_xboole_0(A_27,'#skF_3')
      | ~ r1_xboole_0(A_27,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_74])).

tff(c_82,plain,(
    ! [A_27] : r1_xboole_0(A_27,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_77])).

tff(c_112,plain,(
    ! [A_42,B_43,C_44] :
      ( ~ r1_xboole_0(A_42,B_43)
      | ~ r2_hidden(C_44,B_43)
      | ~ r2_hidden(C_44,A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_117,plain,(
    ! [C_44,A_27] :
      ( ~ r2_hidden(C_44,'#skF_3')
      | ~ r2_hidden(C_44,A_27) ) ),
    inference(resolution,[status(thm)],[c_82,c_112])).

tff(c_182,plain,(
    ! [A_27] : ~ r2_hidden('#skF_2',A_27) ),
    inference(resolution,[status(thm)],[c_155,c_117])).

tff(c_188,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_155])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:47:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.18  
% 1.72/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.18  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.72/1.18  
% 1.72/1.18  %Foreground sorts:
% 1.72/1.18  
% 1.72/1.18  
% 1.72/1.18  %Background operators:
% 1.72/1.18  
% 1.72/1.18  
% 1.72/1.18  %Foreground operators:
% 1.72/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.72/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.72/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.72/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.72/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.72/1.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.72/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.72/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.72/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.72/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.72/1.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.72/1.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.72/1.18  
% 1.96/1.19  tff(f_66, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.96/1.19  tff(f_96, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.96/1.19  tff(f_64, axiom, (![A, B]: ((k2_xboole_0(A, B) = k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_xboole_1)).
% 1.96/1.19  tff(f_88, axiom, (![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l20_zfmisc_1)).
% 1.96/1.19  tff(f_68, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.96/1.19  tff(f_84, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 1.96/1.19  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.96/1.19  tff(c_18, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.96/1.19  tff(c_32, plain, (k2_xboole_0(k1_tarski('#skF_2'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_96])).
% 1.96/1.19  tff(c_39, plain, (![A_22, B_23]: (k1_xboole_0=A_22 | k2_xboole_0(A_22, B_23)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.96/1.19  tff(c_43, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_32, c_39])).
% 1.96/1.19  tff(c_44, plain, (k2_xboole_0(k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_43, c_32])).
% 1.96/1.19  tff(c_105, plain, (![A_40, B_41]: (r2_hidden(A_40, B_41) | ~r1_tarski(k2_xboole_0(k1_tarski(A_40), B_41), B_41))), inference(cnfTransformation, [status(thm)], [f_88])).
% 1.96/1.19  tff(c_150, plain, (![B_51]: (r2_hidden('#skF_2', B_51) | ~r1_tarski(k2_xboole_0(k1_xboole_0, B_51), B_51))), inference(superposition, [status(thm), theory('equality')], [c_43, c_105])).
% 1.96/1.19  tff(c_153, plain, (r2_hidden('#skF_2', '#skF_3') | ~r1_tarski(k1_xboole_0, '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_44, c_150])).
% 1.96/1.19  tff(c_155, plain, (r2_hidden('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_153])).
% 1.96/1.19  tff(c_20, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.96/1.19  tff(c_74, plain, (![A_27, C_28, B_29]: (r1_xboole_0(A_27, C_28) | ~r1_xboole_0(A_27, k2_xboole_0(B_29, C_28)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 1.96/1.19  tff(c_77, plain, (![A_27]: (r1_xboole_0(A_27, '#skF_3') | ~r1_xboole_0(A_27, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_44, c_74])).
% 1.96/1.19  tff(c_82, plain, (![A_27]: (r1_xboole_0(A_27, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_77])).
% 1.96/1.19  tff(c_112, plain, (![A_42, B_43, C_44]: (~r1_xboole_0(A_42, B_43) | ~r2_hidden(C_44, B_43) | ~r2_hidden(C_44, A_42))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.96/1.19  tff(c_117, plain, (![C_44, A_27]: (~r2_hidden(C_44, '#skF_3') | ~r2_hidden(C_44, A_27))), inference(resolution, [status(thm)], [c_82, c_112])).
% 1.96/1.19  tff(c_182, plain, (![A_27]: (~r2_hidden('#skF_2', A_27))), inference(resolution, [status(thm)], [c_155, c_117])).
% 1.96/1.19  tff(c_188, plain, $false, inference(negUnitSimplification, [status(thm)], [c_182, c_155])).
% 1.96/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.19  
% 1.96/1.19  Inference rules
% 1.96/1.19  ----------------------
% 1.96/1.19  #Ref     : 0
% 1.96/1.19  #Sup     : 35
% 1.96/1.19  #Fact    : 0
% 1.96/1.19  #Define  : 0
% 1.96/1.19  #Split   : 0
% 1.96/1.19  #Chain   : 0
% 1.98/1.19  #Close   : 0
% 1.98/1.19  
% 1.98/1.19  Ordering : KBO
% 1.98/1.19  
% 1.98/1.19  Simplification rules
% 1.98/1.19  ----------------------
% 1.98/1.19  #Subsume      : 3
% 1.98/1.19  #Demod        : 12
% 1.98/1.19  #Tautology    : 21
% 1.98/1.19  #SimpNegUnit  : 2
% 1.98/1.19  #BackRed      : 3
% 1.98/1.19  
% 1.98/1.19  #Partial instantiations: 0
% 1.98/1.19  #Strategies tried      : 1
% 1.98/1.19  
% 1.98/1.19  Timing (in seconds)
% 1.98/1.19  ----------------------
% 1.98/1.19  Preprocessing        : 0.27
% 1.98/1.19  Parsing              : 0.15
% 1.98/1.19  CNF conversion       : 0.02
% 1.98/1.19  Main loop            : 0.14
% 1.98/1.19  Inferencing          : 0.06
% 1.98/1.19  Reduction            : 0.04
% 1.98/1.19  Demodulation         : 0.03
% 1.98/1.19  BG Simplification    : 0.01
% 1.98/1.19  Subsumption          : 0.02
% 1.98/1.19  Abstraction          : 0.01
% 1.98/1.19  MUC search           : 0.00
% 1.98/1.19  Cooper               : 0.00
% 1.98/1.19  Total                : 0.44
% 1.98/1.19  Index Insertion      : 0.00
% 1.98/1.19  Index Deletion       : 0.00
% 1.98/1.19  Index Matching       : 0.00
% 1.98/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
