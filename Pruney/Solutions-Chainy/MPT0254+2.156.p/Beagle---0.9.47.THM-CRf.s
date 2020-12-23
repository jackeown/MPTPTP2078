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

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   40 (  78 expanded)
%              Number of leaves         :   21 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   49 ( 100 expanded)
%              Number of equality atoms :   10 (  48 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_98,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( k2_xboole_0(A,B) = k1_xboole_0
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_xboole_1)).

tff(f_86,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
     => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

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

tff(c_34,plain,(
    k2_xboole_0(k1_tarski('#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_50,plain,(
    ! [A_25,B_26] :
      ( k1_xboole_0 = A_25
      | k2_xboole_0(A_25,B_26) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_54,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_50])).

tff(c_56,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_34])).

tff(c_28,plain,(
    ! [A_16] : k2_tarski(A_16,A_16) = k1_tarski(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_201,plain,(
    ! [A_56,C_57,B_58] :
      ( r2_hidden(A_56,C_57)
      | ~ r1_tarski(k2_xboole_0(k2_tarski(A_56,B_58),C_57),C_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_225,plain,(
    ! [A_62,C_63] :
      ( r2_hidden(A_62,C_63)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(A_62),C_63),C_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_201])).

tff(c_232,plain,(
    ! [C_64] :
      ( r2_hidden('#skF_2',C_64)
      | ~ r1_tarski(k2_xboole_0(k1_xboole_0,C_64),C_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_225])).

tff(c_235,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_232])).

tff(c_237,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_235])).

tff(c_20,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_70,plain,(
    ! [A_29,C_30,B_31] :
      ( r1_xboole_0(A_29,C_30)
      | ~ r1_xboole_0(A_29,k2_xboole_0(B_31,C_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_73,plain,(
    ! [A_29] :
      ( r1_xboole_0(A_29,'#skF_3')
      | ~ r1_xboole_0(A_29,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_70])).

tff(c_75,plain,(
    ! [A_29] : r1_xboole_0(A_29,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_73])).

tff(c_116,plain,(
    ! [A_43,B_44,C_45] :
      ( ~ r1_xboole_0(A_43,B_44)
      | ~ r2_hidden(C_45,B_44)
      | ~ r2_hidden(C_45,A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_121,plain,(
    ! [C_45,A_29] :
      ( ~ r2_hidden(C_45,'#skF_3')
      | ~ r2_hidden(C_45,A_29) ) ),
    inference(resolution,[status(thm)],[c_75,c_116])).

tff(c_246,plain,(
    ! [A_29] : ~ r2_hidden('#skF_2',A_29) ),
    inference(resolution,[status(thm)],[c_237,c_121])).

tff(c_295,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_246,c_237])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:55:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.23  
% 2.07/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.23  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.07/1.23  
% 2.07/1.23  %Foreground sorts:
% 2.07/1.23  
% 2.07/1.23  
% 2.07/1.23  %Background operators:
% 2.07/1.23  
% 2.07/1.23  
% 2.07/1.23  %Foreground operators:
% 2.07/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.07/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.07/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.07/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.07/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.07/1.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.07/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.07/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.07/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.07/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.07/1.23  
% 2.07/1.24  tff(f_66, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.07/1.24  tff(f_98, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.07/1.24  tff(f_64, axiom, (![A, B]: ((k2_xboole_0(A, B) = k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_xboole_1)).
% 2.07/1.24  tff(f_86, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.07/1.24  tff(f_94, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 2.07/1.24  tff(f_68, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.07/1.24  tff(f_84, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 2.07/1.24  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.07/1.24  tff(c_18, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.07/1.24  tff(c_34, plain, (k2_xboole_0(k1_tarski('#skF_2'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.07/1.24  tff(c_50, plain, (![A_25, B_26]: (k1_xboole_0=A_25 | k2_xboole_0(A_25, B_26)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.07/1.24  tff(c_54, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_34, c_50])).
% 2.07/1.24  tff(c_56, plain, (k2_xboole_0(k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_54, c_34])).
% 2.07/1.24  tff(c_28, plain, (![A_16]: (k2_tarski(A_16, A_16)=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.07/1.24  tff(c_201, plain, (![A_56, C_57, B_58]: (r2_hidden(A_56, C_57) | ~r1_tarski(k2_xboole_0(k2_tarski(A_56, B_58), C_57), C_57))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.07/1.24  tff(c_225, plain, (![A_62, C_63]: (r2_hidden(A_62, C_63) | ~r1_tarski(k2_xboole_0(k1_tarski(A_62), C_63), C_63))), inference(superposition, [status(thm), theory('equality')], [c_28, c_201])).
% 2.07/1.24  tff(c_232, plain, (![C_64]: (r2_hidden('#skF_2', C_64) | ~r1_tarski(k2_xboole_0(k1_xboole_0, C_64), C_64))), inference(superposition, [status(thm), theory('equality')], [c_54, c_225])).
% 2.07/1.24  tff(c_235, plain, (r2_hidden('#skF_2', '#skF_3') | ~r1_tarski(k1_xboole_0, '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_56, c_232])).
% 2.07/1.24  tff(c_237, plain, (r2_hidden('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_235])).
% 2.07/1.24  tff(c_20, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.07/1.24  tff(c_70, plain, (![A_29, C_30, B_31]: (r1_xboole_0(A_29, C_30) | ~r1_xboole_0(A_29, k2_xboole_0(B_31, C_30)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.07/1.24  tff(c_73, plain, (![A_29]: (r1_xboole_0(A_29, '#skF_3') | ~r1_xboole_0(A_29, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_56, c_70])).
% 2.07/1.24  tff(c_75, plain, (![A_29]: (r1_xboole_0(A_29, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_73])).
% 2.07/1.24  tff(c_116, plain, (![A_43, B_44, C_45]: (~r1_xboole_0(A_43, B_44) | ~r2_hidden(C_45, B_44) | ~r2_hidden(C_45, A_43))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.07/1.24  tff(c_121, plain, (![C_45, A_29]: (~r2_hidden(C_45, '#skF_3') | ~r2_hidden(C_45, A_29))), inference(resolution, [status(thm)], [c_75, c_116])).
% 2.07/1.24  tff(c_246, plain, (![A_29]: (~r2_hidden('#skF_2', A_29))), inference(resolution, [status(thm)], [c_237, c_121])).
% 2.07/1.24  tff(c_295, plain, $false, inference(negUnitSimplification, [status(thm)], [c_246, c_237])).
% 2.07/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.24  
% 2.07/1.24  Inference rules
% 2.07/1.24  ----------------------
% 2.07/1.24  #Ref     : 0
% 2.07/1.24  #Sup     : 57
% 2.07/1.24  #Fact    : 0
% 2.07/1.24  #Define  : 0
% 2.07/1.24  #Split   : 0
% 2.07/1.24  #Chain   : 0
% 2.07/1.24  #Close   : 0
% 2.07/1.24  
% 2.07/1.24  Ordering : KBO
% 2.07/1.24  
% 2.07/1.24  Simplification rules
% 2.07/1.24  ----------------------
% 2.07/1.24  #Subsume      : 4
% 2.07/1.24  #Demod        : 42
% 2.07/1.24  #Tautology    : 42
% 2.07/1.24  #SimpNegUnit  : 1
% 2.07/1.24  #BackRed      : 13
% 2.07/1.24  
% 2.07/1.24  #Partial instantiations: 0
% 2.07/1.24  #Strategies tried      : 1
% 2.07/1.24  
% 2.07/1.24  Timing (in seconds)
% 2.07/1.24  ----------------------
% 2.07/1.25  Preprocessing        : 0.30
% 2.07/1.25  Parsing              : 0.17
% 2.07/1.25  CNF conversion       : 0.02
% 2.07/1.25  Main loop            : 0.16
% 2.07/1.25  Inferencing          : 0.07
% 2.07/1.25  Reduction            : 0.05
% 2.07/1.25  Demodulation         : 0.04
% 2.07/1.25  BG Simplification    : 0.01
% 2.07/1.25  Subsumption          : 0.03
% 2.07/1.25  Abstraction          : 0.01
% 2.07/1.25  MUC search           : 0.00
% 2.07/1.25  Cooper               : 0.00
% 2.07/1.25  Total                : 0.49
% 2.07/1.25  Index Insertion      : 0.00
% 2.07/1.25  Index Deletion       : 0.00
% 2.07/1.25  Index Matching       : 0.00
% 2.07/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
