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
% DateTime   : Thu Dec  3 09:47:27 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   41 (  55 expanded)
%              Number of leaves         :   20 (  28 expanded)
%              Depth                    :   12
%              Number of atoms          :   61 ( 106 expanded)
%              Number of equality atoms :   21 (  27 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > k3_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

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

tff(f_67,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(f_49,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_69,negated_conjecture,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    ! [A_12,C_27] :
      ( r2_hidden('#skF_5'(A_12,k3_tarski(A_12),C_27),A_12)
      | ~ r2_hidden(C_27,k3_tarski(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_44,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(A_34,B_35) = k1_xboole_0
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_48,plain,(
    ! [B_7] : k4_xboole_0(B_7,B_7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_44])).

tff(c_20,plain,(
    ! [A_10,B_11] :
      ( r1_xboole_0(A_10,B_11)
      | k4_xboole_0(A_10,B_11) != A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_78,plain,(
    ! [A_47,B_48,C_49] :
      ( ~ r1_xboole_0(A_47,B_48)
      | ~ r2_hidden(C_49,B_48)
      | ~ r2_hidden(C_49,A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_101,plain,(
    ! [C_55,B_56,A_57] :
      ( ~ r2_hidden(C_55,B_56)
      | ~ r2_hidden(C_55,A_57)
      | k4_xboole_0(A_57,B_56) != A_57 ) ),
    inference(resolution,[status(thm)],[c_20,c_78])).

tff(c_184,plain,(
    ! [A_72,B_73,A_74] :
      ( ~ r2_hidden('#skF_1'(A_72,B_73),A_74)
      | k4_xboole_0(A_74,B_73) != A_74
      | r1_xboole_0(A_72,B_73) ) ),
    inference(resolution,[status(thm)],[c_4,c_101])).

tff(c_194,plain,(
    ! [B_2,A_1] :
      ( k4_xboole_0(B_2,B_2) != B_2
      | r1_xboole_0(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_184])).

tff(c_200,plain,(
    ! [B_75,A_76] :
      ( k1_xboole_0 != B_75
      | r1_xboole_0(A_76,B_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_194])).

tff(c_2,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_228,plain,(
    ! [C_79,B_80,A_81] :
      ( ~ r2_hidden(C_79,B_80)
      | ~ r2_hidden(C_79,A_81)
      | k1_xboole_0 != B_80 ) ),
    inference(resolution,[status(thm)],[c_200,c_2])).

tff(c_526,plain,(
    ! [A_137,C_138,A_139] :
      ( ~ r2_hidden('#skF_5'(A_137,k3_tarski(A_137),C_138),A_139)
      | k1_xboole_0 != A_137
      | ~ r2_hidden(C_138,k3_tarski(A_137)) ) ),
    inference(resolution,[status(thm)],[c_24,c_228])).

tff(c_537,plain,(
    ! [A_140,C_141] :
      ( k1_xboole_0 != A_140
      | ~ r2_hidden(C_141,k3_tarski(A_140)) ) ),
    inference(resolution,[status(thm)],[c_24,c_526])).

tff(c_578,plain,(
    ! [A_144,A_145] :
      ( k1_xboole_0 != A_144
      | r1_xboole_0(A_145,k3_tarski(A_144)) ) ),
    inference(resolution,[status(thm)],[c_4,c_537])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = A_10
      | ~ r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_619,plain,(
    ! [A_148,A_149] :
      ( k4_xboole_0(A_148,k3_tarski(A_149)) = A_148
      | k1_xboole_0 != A_149 ) ),
    inference(resolution,[status(thm)],[c_578,c_18])).

tff(c_665,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_619,c_48])).

tff(c_40,plain,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_668,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_665,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:55:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.48/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.49  
% 2.65/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.50  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > k3_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_4
% 2.65/1.50  
% 2.65/1.50  %Foreground sorts:
% 2.65/1.50  
% 2.65/1.50  
% 2.65/1.50  %Background operators:
% 2.65/1.50  
% 2.65/1.50  
% 2.65/1.50  %Foreground operators:
% 2.65/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.65/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.65/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.65/1.50  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.65/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.65/1.50  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.65/1.50  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.65/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.50  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.65/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.50  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.65/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.65/1.50  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.65/1.50  
% 2.65/1.51  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.65/1.51  tff(f_67, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 2.65/1.51  tff(f_49, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.65/1.51  tff(f_53, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.65/1.51  tff(f_57, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.65/1.51  tff(f_69, negated_conjecture, ~(k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.65/1.51  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.65/1.51  tff(c_24, plain, (![A_12, C_27]: (r2_hidden('#skF_5'(A_12, k3_tarski(A_12), C_27), A_12) | ~r2_hidden(C_27, k3_tarski(A_12)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.65/1.51  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.65/1.51  tff(c_44, plain, (![A_34, B_35]: (k4_xboole_0(A_34, B_35)=k1_xboole_0 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.65/1.51  tff(c_48, plain, (![B_7]: (k4_xboole_0(B_7, B_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_44])).
% 2.65/1.51  tff(c_20, plain, (![A_10, B_11]: (r1_xboole_0(A_10, B_11) | k4_xboole_0(A_10, B_11)!=A_10)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.65/1.51  tff(c_78, plain, (![A_47, B_48, C_49]: (~r1_xboole_0(A_47, B_48) | ~r2_hidden(C_49, B_48) | ~r2_hidden(C_49, A_47))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.65/1.51  tff(c_101, plain, (![C_55, B_56, A_57]: (~r2_hidden(C_55, B_56) | ~r2_hidden(C_55, A_57) | k4_xboole_0(A_57, B_56)!=A_57)), inference(resolution, [status(thm)], [c_20, c_78])).
% 2.65/1.51  tff(c_184, plain, (![A_72, B_73, A_74]: (~r2_hidden('#skF_1'(A_72, B_73), A_74) | k4_xboole_0(A_74, B_73)!=A_74 | r1_xboole_0(A_72, B_73))), inference(resolution, [status(thm)], [c_4, c_101])).
% 2.65/1.51  tff(c_194, plain, (![B_2, A_1]: (k4_xboole_0(B_2, B_2)!=B_2 | r1_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_4, c_184])).
% 2.65/1.51  tff(c_200, plain, (![B_75, A_76]: (k1_xboole_0!=B_75 | r1_xboole_0(A_76, B_75))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_194])).
% 2.65/1.51  tff(c_2, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.65/1.51  tff(c_228, plain, (![C_79, B_80, A_81]: (~r2_hidden(C_79, B_80) | ~r2_hidden(C_79, A_81) | k1_xboole_0!=B_80)), inference(resolution, [status(thm)], [c_200, c_2])).
% 2.65/1.51  tff(c_526, plain, (![A_137, C_138, A_139]: (~r2_hidden('#skF_5'(A_137, k3_tarski(A_137), C_138), A_139) | k1_xboole_0!=A_137 | ~r2_hidden(C_138, k3_tarski(A_137)))), inference(resolution, [status(thm)], [c_24, c_228])).
% 2.65/1.51  tff(c_537, plain, (![A_140, C_141]: (k1_xboole_0!=A_140 | ~r2_hidden(C_141, k3_tarski(A_140)))), inference(resolution, [status(thm)], [c_24, c_526])).
% 2.65/1.51  tff(c_578, plain, (![A_144, A_145]: (k1_xboole_0!=A_144 | r1_xboole_0(A_145, k3_tarski(A_144)))), inference(resolution, [status(thm)], [c_4, c_537])).
% 2.65/1.51  tff(c_18, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=A_10 | ~r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.65/1.51  tff(c_619, plain, (![A_148, A_149]: (k4_xboole_0(A_148, k3_tarski(A_149))=A_148 | k1_xboole_0!=A_149)), inference(resolution, [status(thm)], [c_578, c_18])).
% 2.65/1.51  tff(c_665, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_619, c_48])).
% 2.65/1.51  tff(c_40, plain, (k3_tarski(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.65/1.51  tff(c_668, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_665, c_40])).
% 2.65/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.51  
% 2.65/1.51  Inference rules
% 2.65/1.51  ----------------------
% 2.65/1.51  #Ref     : 2
% 2.65/1.51  #Sup     : 145
% 2.65/1.51  #Fact    : 0
% 2.65/1.51  #Define  : 0
% 2.65/1.51  #Split   : 0
% 2.65/1.51  #Chain   : 0
% 2.65/1.51  #Close   : 0
% 2.65/1.51  
% 2.65/1.51  Ordering : KBO
% 2.65/1.51  
% 2.65/1.51  Simplification rules
% 2.65/1.51  ----------------------
% 2.65/1.51  #Subsume      : 27
% 2.65/1.51  #Demod        : 10
% 2.65/1.51  #Tautology    : 29
% 2.65/1.51  #SimpNegUnit  : 0
% 2.65/1.51  #BackRed      : 1
% 2.65/1.51  
% 2.65/1.51  #Partial instantiations: 0
% 2.65/1.51  #Strategies tried      : 1
% 2.65/1.51  
% 2.65/1.51  Timing (in seconds)
% 2.65/1.51  ----------------------
% 2.65/1.51  Preprocessing        : 0.29
% 2.65/1.51  Parsing              : 0.15
% 2.65/1.51  CNF conversion       : 0.02
% 2.65/1.51  Main loop            : 0.31
% 2.65/1.51  Inferencing          : 0.12
% 2.65/1.51  Reduction            : 0.07
% 2.65/1.51  Demodulation         : 0.05
% 2.65/1.51  BG Simplification    : 0.02
% 2.65/1.51  Subsumption          : 0.08
% 2.65/1.51  Abstraction          : 0.02
% 2.65/1.51  MUC search           : 0.00
% 2.65/1.51  Cooper               : 0.00
% 2.65/1.51  Total                : 0.64
% 2.65/1.51  Index Insertion      : 0.00
% 2.65/1.51  Index Deletion       : 0.00
% 2.65/1.51  Index Matching       : 0.00
% 2.65/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
