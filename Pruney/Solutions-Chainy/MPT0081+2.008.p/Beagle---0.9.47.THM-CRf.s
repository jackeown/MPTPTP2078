%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:57 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :   40 (  46 expanded)
%              Number of leaves         :   20 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   46 (  56 expanded)
%              Number of equality atoms :   17 (  22 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_49,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,k3_xboole_0(B,C))
          & r1_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),A_5)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_187,plain,(
    ! [A_43,B_44,C_45] :
      ( ~ r1_xboole_0(A_43,B_44)
      | ~ r2_hidden(C_45,k3_xboole_0(A_43,B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_324,plain,(
    ! [A_54,C_55] :
      ( ~ r1_xboole_0(A_54,A_54)
      | ~ r2_hidden(C_55,A_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_187])).

tff(c_333,plain,(
    ! [C_55,B_2] :
      ( ~ r2_hidden(C_55,B_2)
      | k3_xboole_0(B_2,B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_324])).

tff(c_341,plain,(
    ! [C_56,B_57] :
      ( ~ r2_hidden(C_56,B_57)
      | k1_xboole_0 != B_57 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_333])).

tff(c_352,plain,(
    ! [A_58,B_59] :
      ( k1_xboole_0 != A_58
      | r1_xboole_0(A_58,B_59) ) ),
    inference(resolution,[status(thm)],[c_12,c_341])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_404,plain,(
    ! [B_59] : k3_xboole_0(k1_xboole_0,B_59) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_352,c_2])).

tff(c_28,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_61,plain,(
    ! [A_30,B_31] :
      ( k3_xboole_0(A_30,B_31) = k1_xboole_0
      | ~ r1_xboole_0(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_65,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_61])).

tff(c_530,plain,(
    ! [A_70,B_71,C_72] : k3_xboole_0(k3_xboole_0(A_70,B_71),C_72) = k3_xboole_0(A_70,k3_xboole_0(B_71,C_72)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_581,plain,(
    ! [C_72] : k3_xboole_0('#skF_3',k3_xboole_0('#skF_4',C_72)) = k3_xboole_0(k1_xboole_0,C_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_530])).

tff(c_595,plain,(
    ! [C_72] : k3_xboole_0('#skF_3',k3_xboole_0('#skF_4',C_72)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_581])).

tff(c_77,plain,(
    ! [A_32,B_33] :
      ( r1_xboole_0(A_32,B_33)
      | k3_xboole_0(A_32,B_33) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_30,plain,(
    ~ r1_xboole_0('#skF_3',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_85,plain,(
    k3_xboole_0('#skF_3',k3_xboole_0('#skF_4','#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_77,c_30])).

tff(c_598,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_595,c_85])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:50:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.37  
% 2.18/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.37  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.44/1.37  
% 2.44/1.37  %Foreground sorts:
% 2.44/1.37  
% 2.44/1.37  
% 2.44/1.37  %Background operators:
% 2.44/1.37  
% 2.44/1.37  
% 2.44/1.37  %Foreground operators:
% 2.44/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.44/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.44/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.44/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.44/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.44/1.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.44/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.44/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.44/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.44/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.44/1.37  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.44/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.44/1.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.44/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.44/1.37  
% 2.44/1.38  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.44/1.38  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.44/1.38  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.44/1.38  tff(f_63, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.44/1.38  tff(f_80, negated_conjecture, ~(![A, B, C]: ~(~r1_xboole_0(A, k3_xboole_0(B, C)) & r1_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_xboole_1)).
% 2.44/1.38  tff(f_65, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 2.44/1.38  tff(c_12, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), A_5) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.44/1.38  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.44/1.38  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.44/1.38  tff(c_187, plain, (![A_43, B_44, C_45]: (~r1_xboole_0(A_43, B_44) | ~r2_hidden(C_45, k3_xboole_0(A_43, B_44)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.44/1.38  tff(c_324, plain, (![A_54, C_55]: (~r1_xboole_0(A_54, A_54) | ~r2_hidden(C_55, A_54))), inference(superposition, [status(thm), theory('equality')], [c_6, c_187])).
% 2.44/1.38  tff(c_333, plain, (![C_55, B_2]: (~r2_hidden(C_55, B_2) | k3_xboole_0(B_2, B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_324])).
% 2.44/1.38  tff(c_341, plain, (![C_56, B_57]: (~r2_hidden(C_56, B_57) | k1_xboole_0!=B_57)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_333])).
% 2.44/1.38  tff(c_352, plain, (![A_58, B_59]: (k1_xboole_0!=A_58 | r1_xboole_0(A_58, B_59))), inference(resolution, [status(thm)], [c_12, c_341])).
% 2.44/1.38  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.44/1.38  tff(c_404, plain, (![B_59]: (k3_xboole_0(k1_xboole_0, B_59)=k1_xboole_0)), inference(resolution, [status(thm)], [c_352, c_2])).
% 2.44/1.38  tff(c_28, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.44/1.38  tff(c_61, plain, (![A_30, B_31]: (k3_xboole_0(A_30, B_31)=k1_xboole_0 | ~r1_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.44/1.38  tff(c_65, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_61])).
% 2.44/1.38  tff(c_530, plain, (![A_70, B_71, C_72]: (k3_xboole_0(k3_xboole_0(A_70, B_71), C_72)=k3_xboole_0(A_70, k3_xboole_0(B_71, C_72)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.44/1.38  tff(c_581, plain, (![C_72]: (k3_xboole_0('#skF_3', k3_xboole_0('#skF_4', C_72))=k3_xboole_0(k1_xboole_0, C_72))), inference(superposition, [status(thm), theory('equality')], [c_65, c_530])).
% 2.44/1.38  tff(c_595, plain, (![C_72]: (k3_xboole_0('#skF_3', k3_xboole_0('#skF_4', C_72))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_404, c_581])).
% 2.44/1.38  tff(c_77, plain, (![A_32, B_33]: (r1_xboole_0(A_32, B_33) | k3_xboole_0(A_32, B_33)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.44/1.38  tff(c_30, plain, (~r1_xboole_0('#skF_3', k3_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.44/1.38  tff(c_85, plain, (k3_xboole_0('#skF_3', k3_xboole_0('#skF_4', '#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_77, c_30])).
% 2.44/1.38  tff(c_598, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_595, c_85])).
% 2.44/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.38  
% 2.44/1.38  Inference rules
% 2.44/1.38  ----------------------
% 2.44/1.38  #Ref     : 0
% 2.44/1.38  #Sup     : 141
% 2.44/1.38  #Fact    : 0
% 2.44/1.38  #Define  : 0
% 2.44/1.38  #Split   : 0
% 2.44/1.38  #Chain   : 0
% 2.44/1.38  #Close   : 0
% 2.44/1.38  
% 2.44/1.38  Ordering : KBO
% 2.44/1.38  
% 2.44/1.38  Simplification rules
% 2.44/1.38  ----------------------
% 2.44/1.38  #Subsume      : 22
% 2.44/1.38  #Demod        : 40
% 2.44/1.38  #Tautology    : 70
% 2.44/1.38  #SimpNegUnit  : 0
% 2.44/1.38  #BackRed      : 1
% 2.44/1.38  
% 2.44/1.38  #Partial instantiations: 0
% 2.44/1.38  #Strategies tried      : 1
% 2.44/1.38  
% 2.44/1.38  Timing (in seconds)
% 2.44/1.38  ----------------------
% 2.44/1.39  Preprocessing        : 0.27
% 2.44/1.39  Parsing              : 0.16
% 2.44/1.39  CNF conversion       : 0.02
% 2.44/1.39  Main loop            : 0.34
% 2.44/1.39  Inferencing          : 0.16
% 2.44/1.39  Reduction            : 0.10
% 2.44/1.39  Demodulation         : 0.07
% 2.44/1.39  BG Simplification    : 0.01
% 2.44/1.39  Subsumption          : 0.05
% 2.44/1.39  Abstraction          : 0.01
% 2.44/1.39  MUC search           : 0.00
% 2.44/1.39  Cooper               : 0.00
% 2.44/1.39  Total                : 0.64
% 2.44/1.39  Index Insertion      : 0.00
% 2.44/1.39  Index Deletion       : 0.00
% 2.44/1.39  Index Matching       : 0.00
% 2.44/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
