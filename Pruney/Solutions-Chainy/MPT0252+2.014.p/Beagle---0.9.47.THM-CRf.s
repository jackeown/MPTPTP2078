%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:03 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :   45 (  50 expanded)
%              Number of leaves         :   25 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :   43 (  51 expanded)
%              Number of equality atoms :    7 (  10 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_58,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_34,plain,(
    ~ r2_hidden('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_161,plain,(
    ! [A_61,B_62] :
      ( ~ r2_hidden('#skF_1'(A_61,B_62),B_62)
      | r1_tarski(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_166,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_161])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,k2_xboole_0(C_8,B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_12,plain,(
    ! [B_13,A_12] : k2_tarski(B_13,A_12) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_71,plain,(
    ! [A_48,B_49] : k3_tarski(k2_tarski(A_48,B_49)) = k2_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_96,plain,(
    ! [B_54,A_55] : k3_tarski(k2_tarski(B_54,A_55)) = k2_xboole_0(A_55,B_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_71])).

tff(c_26,plain,(
    ! [A_41,B_42] : k3_tarski(k2_tarski(A_41,B_42)) = k2_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_102,plain,(
    ! [B_54,A_55] : k2_xboole_0(B_54,A_55) = k2_xboole_0(A_55,B_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_26])).

tff(c_36,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_2','#skF_3'),'#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_37,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_3','#skF_2'),'#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_36])).

tff(c_119,plain,(
    r1_tarski(k2_xboole_0('#skF_4',k2_tarski('#skF_3','#skF_2')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_37])).

tff(c_256,plain,(
    ! [A_83,C_84,B_85] :
      ( r1_tarski(A_83,C_84)
      | ~ r1_tarski(B_85,C_84)
      | ~ r1_tarski(A_83,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_304,plain,(
    ! [A_93] :
      ( r1_tarski(A_93,'#skF_4')
      | ~ r1_tarski(A_93,k2_xboole_0('#skF_4',k2_tarski('#skF_3','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_119,c_256])).

tff(c_397,plain,(
    ! [A_107] :
      ( r1_tarski(A_107,'#skF_4')
      | ~ r1_tarski(A_107,k2_tarski('#skF_3','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_8,c_304])).

tff(c_402,plain,(
    r1_tarski(k2_tarski('#skF_3','#skF_2'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_166,c_397])).

tff(c_30,plain,(
    ! [B_44,C_45,A_43] :
      ( r2_hidden(B_44,C_45)
      | ~ r1_tarski(k2_tarski(A_43,B_44),C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_409,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_402,c_30])).

tff(c_418,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_409])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:20:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.32  
% 2.06/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.32  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.06/1.32  
% 2.06/1.32  %Foreground sorts:
% 2.06/1.32  
% 2.06/1.32  
% 2.06/1.32  %Background operators:
% 2.06/1.32  
% 2.06/1.32  
% 2.06/1.32  %Foreground operators:
% 2.06/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.06/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.06/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.06/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.06/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.06/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.06/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.06/1.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.06/1.32  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.06/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.32  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.06/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.06/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.06/1.32  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.06/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.06/1.32  
% 2.44/1.33  tff(f_69, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 2.44/1.33  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.44/1.33  tff(f_36, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.44/1.33  tff(f_44, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.44/1.33  tff(f_58, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.44/1.33  tff(f_42, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.44/1.33  tff(f_64, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.44/1.33  tff(c_34, plain, (~r2_hidden('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.44/1.33  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.44/1.33  tff(c_161, plain, (![A_61, B_62]: (~r2_hidden('#skF_1'(A_61, B_62), B_62) | r1_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.44/1.33  tff(c_166, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_161])).
% 2.44/1.33  tff(c_8, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, k2_xboole_0(C_8, B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.44/1.33  tff(c_12, plain, (![B_13, A_12]: (k2_tarski(B_13, A_12)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.44/1.33  tff(c_71, plain, (![A_48, B_49]: (k3_tarski(k2_tarski(A_48, B_49))=k2_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.44/1.33  tff(c_96, plain, (![B_54, A_55]: (k3_tarski(k2_tarski(B_54, A_55))=k2_xboole_0(A_55, B_54))), inference(superposition, [status(thm), theory('equality')], [c_12, c_71])).
% 2.44/1.33  tff(c_26, plain, (![A_41, B_42]: (k3_tarski(k2_tarski(A_41, B_42))=k2_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.44/1.33  tff(c_102, plain, (![B_54, A_55]: (k2_xboole_0(B_54, A_55)=k2_xboole_0(A_55, B_54))), inference(superposition, [status(thm), theory('equality')], [c_96, c_26])).
% 2.44/1.33  tff(c_36, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_2', '#skF_3'), '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.44/1.33  tff(c_37, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_3', '#skF_2'), '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_36])).
% 2.44/1.33  tff(c_119, plain, (r1_tarski(k2_xboole_0('#skF_4', k2_tarski('#skF_3', '#skF_2')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_37])).
% 2.44/1.33  tff(c_256, plain, (![A_83, C_84, B_85]: (r1_tarski(A_83, C_84) | ~r1_tarski(B_85, C_84) | ~r1_tarski(A_83, B_85))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.44/1.33  tff(c_304, plain, (![A_93]: (r1_tarski(A_93, '#skF_4') | ~r1_tarski(A_93, k2_xboole_0('#skF_4', k2_tarski('#skF_3', '#skF_2'))))), inference(resolution, [status(thm)], [c_119, c_256])).
% 2.44/1.33  tff(c_397, plain, (![A_107]: (r1_tarski(A_107, '#skF_4') | ~r1_tarski(A_107, k2_tarski('#skF_3', '#skF_2')))), inference(resolution, [status(thm)], [c_8, c_304])).
% 2.44/1.33  tff(c_402, plain, (r1_tarski(k2_tarski('#skF_3', '#skF_2'), '#skF_4')), inference(resolution, [status(thm)], [c_166, c_397])).
% 2.44/1.33  tff(c_30, plain, (![B_44, C_45, A_43]: (r2_hidden(B_44, C_45) | ~r1_tarski(k2_tarski(A_43, B_44), C_45))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.44/1.33  tff(c_409, plain, (r2_hidden('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_402, c_30])).
% 2.44/1.33  tff(c_418, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_409])).
% 2.44/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.33  
% 2.44/1.33  Inference rules
% 2.44/1.33  ----------------------
% 2.44/1.33  #Ref     : 0
% 2.44/1.33  #Sup     : 91
% 2.44/1.33  #Fact    : 0
% 2.44/1.33  #Define  : 0
% 2.44/1.33  #Split   : 0
% 2.44/1.33  #Chain   : 0
% 2.44/1.33  #Close   : 0
% 2.44/1.33  
% 2.44/1.33  Ordering : KBO
% 2.44/1.33  
% 2.44/1.34  Simplification rules
% 2.44/1.34  ----------------------
% 2.44/1.34  #Subsume      : 11
% 2.44/1.34  #Demod        : 23
% 2.44/1.34  #Tautology    : 49
% 2.44/1.34  #SimpNegUnit  : 1
% 2.44/1.34  #BackRed      : 1
% 2.44/1.34  
% 2.44/1.34  #Partial instantiations: 0
% 2.44/1.34  #Strategies tried      : 1
% 2.44/1.34  
% 2.44/1.34  Timing (in seconds)
% 2.44/1.34  ----------------------
% 2.44/1.34  Preprocessing        : 0.30
% 2.44/1.34  Parsing              : 0.16
% 2.44/1.34  CNF conversion       : 0.02
% 2.44/1.34  Main loop            : 0.23
% 2.44/1.34  Inferencing          : 0.08
% 2.44/1.34  Reduction            : 0.09
% 2.44/1.34  Demodulation         : 0.07
% 2.44/1.34  BG Simplification    : 0.02
% 2.44/1.34  Subsumption          : 0.04
% 2.44/1.34  Abstraction          : 0.01
% 2.44/1.34  MUC search           : 0.00
% 2.44/1.34  Cooper               : 0.00
% 2.44/1.34  Total                : 0.56
% 2.44/1.34  Index Insertion      : 0.00
% 2.44/1.34  Index Deletion       : 0.00
% 2.44/1.34  Index Matching       : 0.00
% 2.44/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
