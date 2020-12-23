%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:55 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   36 (  46 expanded)
%              Number of leaves         :   21 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   47 (  60 expanded)
%              Number of equality atoms :    3 (   7 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

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

tff(f_75,axiom,(
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

tff(c_40,plain,(
    k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_47,plain,(
    ! [A_20,C_21,B_22] :
      ( r1_xboole_0(A_20,C_21)
      | ~ r1_xboole_0(A_20,k2_xboole_0(B_22,C_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_50,plain,(
    ! [A_20] :
      ( r1_xboole_0(A_20,'#skF_5')
      | ~ r1_xboole_0(A_20,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_47])).

tff(c_52,plain,(
    ! [A_20] : r1_xboole_0(A_20,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_50])).

tff(c_28,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_71,plain,(
    ! [A_36,C_37,B_38] :
      ( r2_hidden(A_36,C_37)
      | ~ r1_tarski(k2_xboole_0(k2_tarski(A_36,B_38),C_37),C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_74,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | ~ r1_tarski(k1_xboole_0,'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_71])).

tff(c_76,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_74])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( ~ r2_hidden(D_6,A_1)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_122,plain,(
    ! [C_49,B_50,A_51] :
      ( ~ r2_hidden(C_49,B_50)
      | ~ r2_hidden(C_49,A_51)
      | ~ r2_hidden(C_49,k2_xboole_0(A_51,B_50))
      | ~ r1_xboole_0(A_51,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_141,plain,(
    ! [D_53,B_54,A_55] :
      ( ~ r2_hidden(D_53,B_54)
      | ~ r1_xboole_0(A_55,B_54)
      | ~ r2_hidden(D_53,A_55) ) ),
    inference(resolution,[status(thm)],[c_6,c_122])).

tff(c_145,plain,(
    ! [A_55] :
      ( ~ r1_xboole_0(A_55,'#skF_5')
      | ~ r2_hidden('#skF_3',A_55) ) ),
    inference(resolution,[status(thm)],[c_76,c_141])).

tff(c_157,plain,(
    ! [A_55] : ~ r2_hidden('#skF_3',A_55) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_145])).

tff(c_164,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_157,c_76])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:45:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.17  
% 1.70/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.17  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 1.70/1.17  
% 1.70/1.17  %Foreground sorts:
% 1.70/1.17  
% 1.70/1.17  
% 1.70/1.17  %Background operators:
% 1.70/1.17  
% 1.70/1.17  
% 1.70/1.17  %Foreground operators:
% 1.70/1.17  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.70/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.70/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.70/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.70/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.70/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.70/1.17  tff('#skF_5', type, '#skF_5': $i).
% 1.70/1.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.70/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.70/1.17  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.70/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.70/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.70/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.70/1.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.70/1.18  
% 1.94/1.18  tff(f_55, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.94/1.18  tff(f_79, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 1.94/1.18  tff(f_71, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 1.94/1.18  tff(f_53, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.94/1.18  tff(f_75, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 1.94/1.18  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 1.94/1.18  tff(f_51, axiom, (![A, B, C]: ~(((r1_xboole_0(A, B) & r2_hidden(C, k2_xboole_0(A, B))) & ~(r2_hidden(C, A) & ~r2_hidden(C, B))) & ~(r2_hidden(C, B) & ~r2_hidden(C, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_xboole_0)).
% 1.94/1.18  tff(c_30, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.94/1.18  tff(c_40, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.94/1.18  tff(c_47, plain, (![A_20, C_21, B_22]: (r1_xboole_0(A_20, C_21) | ~r1_xboole_0(A_20, k2_xboole_0(B_22, C_21)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.94/1.18  tff(c_50, plain, (![A_20]: (r1_xboole_0(A_20, '#skF_5') | ~r1_xboole_0(A_20, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_40, c_47])).
% 1.94/1.18  tff(c_52, plain, (![A_20]: (r1_xboole_0(A_20, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_50])).
% 1.94/1.18  tff(c_28, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.94/1.18  tff(c_71, plain, (![A_36, C_37, B_38]: (r2_hidden(A_36, C_37) | ~r1_tarski(k2_xboole_0(k2_tarski(A_36, B_38), C_37), C_37))), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.94/1.18  tff(c_74, plain, (r2_hidden('#skF_3', '#skF_5') | ~r1_tarski(k1_xboole_0, '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_40, c_71])).
% 1.94/1.18  tff(c_76, plain, (r2_hidden('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_74])).
% 1.94/1.18  tff(c_6, plain, (![D_6, A_1, B_2]: (~r2_hidden(D_6, A_1) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.94/1.18  tff(c_122, plain, (![C_49, B_50, A_51]: (~r2_hidden(C_49, B_50) | ~r2_hidden(C_49, A_51) | ~r2_hidden(C_49, k2_xboole_0(A_51, B_50)) | ~r1_xboole_0(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.94/1.18  tff(c_141, plain, (![D_53, B_54, A_55]: (~r2_hidden(D_53, B_54) | ~r1_xboole_0(A_55, B_54) | ~r2_hidden(D_53, A_55))), inference(resolution, [status(thm)], [c_6, c_122])).
% 1.94/1.18  tff(c_145, plain, (![A_55]: (~r1_xboole_0(A_55, '#skF_5') | ~r2_hidden('#skF_3', A_55))), inference(resolution, [status(thm)], [c_76, c_141])).
% 1.94/1.18  tff(c_157, plain, (![A_55]: (~r2_hidden('#skF_3', A_55))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_145])).
% 1.94/1.18  tff(c_164, plain, $false, inference(negUnitSimplification, [status(thm)], [c_157, c_76])).
% 1.94/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.18  
% 1.94/1.18  Inference rules
% 1.94/1.18  ----------------------
% 1.94/1.18  #Ref     : 0
% 1.94/1.18  #Sup     : 26
% 1.94/1.18  #Fact    : 0
% 1.94/1.18  #Define  : 0
% 1.94/1.18  #Split   : 0
% 1.94/1.18  #Chain   : 0
% 1.94/1.18  #Close   : 0
% 1.94/1.18  
% 1.94/1.18  Ordering : KBO
% 1.94/1.18  
% 1.94/1.18  Simplification rules
% 1.94/1.18  ----------------------
% 1.94/1.18  #Subsume      : 2
% 1.94/1.18  #Demod        : 11
% 1.94/1.18  #Tautology    : 13
% 1.94/1.18  #SimpNegUnit  : 1
% 1.94/1.18  #BackRed      : 1
% 1.94/1.19  
% 1.94/1.19  #Partial instantiations: 0
% 1.94/1.19  #Strategies tried      : 1
% 1.94/1.19  
% 1.94/1.19  Timing (in seconds)
% 1.94/1.19  ----------------------
% 1.98/1.19  Preprocessing        : 0.27
% 1.98/1.19  Parsing              : 0.15
% 1.98/1.19  CNF conversion       : 0.02
% 1.98/1.19  Main loop            : 0.15
% 1.98/1.19  Inferencing          : 0.06
% 1.98/1.19  Reduction            : 0.04
% 1.98/1.19  Demodulation         : 0.03
% 1.98/1.19  BG Simplification    : 0.01
% 1.98/1.19  Subsumption          : 0.03
% 1.98/1.19  Abstraction          : 0.01
% 1.98/1.19  MUC search           : 0.00
% 1.98/1.19  Cooper               : 0.00
% 1.98/1.19  Total                : 0.45
% 1.98/1.19  Index Insertion      : 0.00
% 1.98/1.19  Index Deletion       : 0.00
% 1.98/1.19  Index Matching       : 0.00
% 1.98/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
