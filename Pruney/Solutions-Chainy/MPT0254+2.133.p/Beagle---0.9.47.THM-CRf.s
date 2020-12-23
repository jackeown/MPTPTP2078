%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:36 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   39 (  52 expanded)
%              Number of leaves         :   22 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   51 (  68 expanded)
%              Number of equality atoms :    5 (  11 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_55,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_53,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_73,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
     => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(A,B)
        & r2_hidden(C,k2_xboole_0(A,B))
        & ~ ( r2_hidden(C,A)
            & ~ r2_hidden(C,B) )
        & ~ ( r2_hidden(C,B)
            & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_0)).

tff(c_30,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_42,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_70,plain,(
    ! [A_30,C_31,B_32] :
      ( r1_xboole_0(A_30,C_31)
      | ~ r1_xboole_0(A_30,k2_xboole_0(B_32,C_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_73,plain,(
    ! [A_30] :
      ( r1_xboole_0(A_30,'#skF_4')
      | ~ r1_xboole_0(A_30,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_70])).

tff(c_75,plain,(
    ! [A_30] : r1_xboole_0(A_30,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_73])).

tff(c_28,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_38,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_82,plain,(
    ! [A_38,C_39,B_40] :
      ( r2_hidden(A_38,C_39)
      | ~ r1_tarski(k2_xboole_0(k2_tarski(A_38,B_40),C_39),C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_86,plain,(
    ! [A_41,C_42] :
      ( r2_hidden(A_41,C_42)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(A_41),C_42),C_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_82])).

tff(c_89,plain,
    ( r2_hidden('#skF_3','#skF_4')
    | ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_86])).

tff(c_91,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_89])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( ~ r2_hidden(D_6,A_1)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_123,plain,(
    ! [C_50,B_51,A_52] :
      ( ~ r2_hidden(C_50,B_51)
      | ~ r2_hidden(C_50,A_52)
      | ~ r2_hidden(C_50,k2_xboole_0(A_52,B_51))
      | ~ r1_xboole_0(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_142,plain,(
    ! [D_54,B_55,A_56] :
      ( ~ r2_hidden(D_54,B_55)
      | ~ r1_xboole_0(A_56,B_55)
      | ~ r2_hidden(D_54,A_56) ) ),
    inference(resolution,[status(thm)],[c_6,c_123])).

tff(c_146,plain,(
    ! [A_56] :
      ( ~ r1_xboole_0(A_56,'#skF_4')
      | ~ r2_hidden('#skF_3',A_56) ) ),
    inference(resolution,[status(thm)],[c_91,c_142])).

tff(c_158,plain,(
    ! [A_56] : ~ r2_hidden('#skF_3',A_56) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_146])).

tff(c_165,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_158,c_91])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:17:45 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.17  
% 1.90/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.17  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 1.90/1.17  
% 1.90/1.17  %Foreground sorts:
% 1.90/1.17  
% 1.90/1.17  
% 1.90/1.17  %Background operators:
% 1.90/1.17  
% 1.90/1.17  
% 1.90/1.17  %Foreground operators:
% 1.90/1.17  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.90/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.90/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.90/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.90/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.90/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.90/1.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.90/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.90/1.17  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.90/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.90/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.90/1.17  
% 1.90/1.18  tff(f_55, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.90/1.18  tff(f_81, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.90/1.18  tff(f_71, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 1.90/1.18  tff(f_53, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.90/1.18  tff(f_73, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.90/1.18  tff(f_77, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 1.90/1.18  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 1.90/1.18  tff(f_51, axiom, (![A, B, C]: ~(((r1_xboole_0(A, B) & r2_hidden(C, k2_xboole_0(A, B))) & ~(r2_hidden(C, A) & ~r2_hidden(C, B))) & ~(r2_hidden(C, B) & ~r2_hidden(C, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_xboole_0)).
% 1.90/1.18  tff(c_30, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.90/1.18  tff(c_42, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.90/1.18  tff(c_70, plain, (![A_30, C_31, B_32]: (r1_xboole_0(A_30, C_31) | ~r1_xboole_0(A_30, k2_xboole_0(B_32, C_31)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.90/1.18  tff(c_73, plain, (![A_30]: (r1_xboole_0(A_30, '#skF_4') | ~r1_xboole_0(A_30, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_42, c_70])).
% 1.90/1.18  tff(c_75, plain, (![A_30]: (r1_xboole_0(A_30, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_73])).
% 1.90/1.18  tff(c_28, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.90/1.18  tff(c_38, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.90/1.18  tff(c_82, plain, (![A_38, C_39, B_40]: (r2_hidden(A_38, C_39) | ~r1_tarski(k2_xboole_0(k2_tarski(A_38, B_40), C_39), C_39))), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.90/1.18  tff(c_86, plain, (![A_41, C_42]: (r2_hidden(A_41, C_42) | ~r1_tarski(k2_xboole_0(k1_tarski(A_41), C_42), C_42))), inference(superposition, [status(thm), theory('equality')], [c_38, c_82])).
% 1.90/1.18  tff(c_89, plain, (r2_hidden('#skF_3', '#skF_4') | ~r1_tarski(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_42, c_86])).
% 1.90/1.18  tff(c_91, plain, (r2_hidden('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_89])).
% 1.90/1.18  tff(c_6, plain, (![D_6, A_1, B_2]: (~r2_hidden(D_6, A_1) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.90/1.18  tff(c_123, plain, (![C_50, B_51, A_52]: (~r2_hidden(C_50, B_51) | ~r2_hidden(C_50, A_52) | ~r2_hidden(C_50, k2_xboole_0(A_52, B_51)) | ~r1_xboole_0(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.90/1.18  tff(c_142, plain, (![D_54, B_55, A_56]: (~r2_hidden(D_54, B_55) | ~r1_xboole_0(A_56, B_55) | ~r2_hidden(D_54, A_56))), inference(resolution, [status(thm)], [c_6, c_123])).
% 1.90/1.18  tff(c_146, plain, (![A_56]: (~r1_xboole_0(A_56, '#skF_4') | ~r2_hidden('#skF_3', A_56))), inference(resolution, [status(thm)], [c_91, c_142])).
% 1.90/1.18  tff(c_158, plain, (![A_56]: (~r2_hidden('#skF_3', A_56))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_146])).
% 1.90/1.18  tff(c_165, plain, $false, inference(negUnitSimplification, [status(thm)], [c_158, c_91])).
% 1.90/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.18  
% 1.90/1.18  Inference rules
% 1.90/1.18  ----------------------
% 1.90/1.18  #Ref     : 0
% 1.90/1.18  #Sup     : 26
% 1.90/1.18  #Fact    : 0
% 1.90/1.18  #Define  : 0
% 1.90/1.18  #Split   : 0
% 1.90/1.18  #Chain   : 0
% 1.90/1.18  #Close   : 0
% 1.90/1.18  
% 1.90/1.18  Ordering : KBO
% 1.90/1.18  
% 1.90/1.18  Simplification rules
% 1.90/1.18  ----------------------
% 1.90/1.18  #Subsume      : 1
% 1.90/1.18  #Demod        : 10
% 1.90/1.18  #Tautology    : 13
% 1.90/1.18  #SimpNegUnit  : 1
% 1.90/1.18  #BackRed      : 1
% 1.90/1.18  
% 1.90/1.18  #Partial instantiations: 0
% 1.90/1.18  #Strategies tried      : 1
% 1.90/1.18  
% 1.90/1.18  Timing (in seconds)
% 1.90/1.18  ----------------------
% 1.90/1.18  Preprocessing        : 0.29
% 1.90/1.18  Parsing              : 0.15
% 1.90/1.18  CNF conversion       : 0.02
% 1.90/1.18  Main loop            : 0.14
% 1.90/1.18  Inferencing          : 0.05
% 1.90/1.18  Reduction            : 0.04
% 1.90/1.18  Demodulation         : 0.03
% 1.90/1.18  BG Simplification    : 0.01
% 1.90/1.18  Subsumption          : 0.03
% 1.90/1.18  Abstraction          : 0.01
% 1.90/1.18  MUC search           : 0.00
% 1.90/1.18  Cooper               : 0.00
% 1.90/1.18  Total                : 0.46
% 1.90/1.18  Index Insertion      : 0.00
% 1.90/1.18  Index Deletion       : 0.00
% 1.90/1.18  Index Matching       : 0.00
% 1.90/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
