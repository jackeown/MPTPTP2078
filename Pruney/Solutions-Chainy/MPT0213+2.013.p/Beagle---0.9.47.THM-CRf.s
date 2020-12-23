%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:28 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :   41 (  47 expanded)
%              Number of leaves         :   22 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :   55 (  81 expanded)
%              Number of equality atoms :   20 (  21 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_6 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(f_53,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

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

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_71,negated_conjecture,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_20,plain,(
    ! [A_13,C_28] :
      ( r2_hidden('#skF_6'(A_13,k3_tarski(A_13),C_28),A_13)
      | ~ r2_hidden(C_28,k3_tarski(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_10,plain,(
    ! [A_8] : k2_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_46,plain,(
    ! [A_33,B_34] : k4_xboole_0(A_33,k2_xboole_0(A_33,B_34)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_53,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_46])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( r1_xboole_0(A_11,B_12)
      | k4_xboole_0(A_11,B_12) != A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_72,plain,(
    ! [A_45,B_46,C_47] :
      ( ~ r1_xboole_0(A_45,B_46)
      | ~ r2_hidden(C_47,B_46)
      | ~ r2_hidden(C_47,A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_86,plain,(
    ! [C_51,B_52,A_53] :
      ( ~ r2_hidden(C_51,B_52)
      | ~ r2_hidden(C_51,A_53)
      | k4_xboole_0(A_53,B_52) != A_53 ) ),
    inference(resolution,[status(thm)],[c_16,c_72])).

tff(c_167,plain,(
    ! [A_68,B_69,A_70] :
      ( ~ r2_hidden('#skF_1'(A_68,B_69),A_70)
      | k4_xboole_0(A_70,B_69) != A_70
      | r1_xboole_0(A_68,B_69) ) ),
    inference(resolution,[status(thm)],[c_4,c_86])).

tff(c_178,plain,(
    ! [B_2,A_1] :
      ( k4_xboole_0(B_2,B_2) != B_2
      | r1_xboole_0(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_167])).

tff(c_194,plain,(
    ! [B_73,A_74] :
      ( k1_xboole_0 != B_73
      | r1_xboole_0(A_74,B_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_178])).

tff(c_2,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_231,plain,(
    ! [C_79,B_80,A_81] :
      ( ~ r2_hidden(C_79,B_80)
      | ~ r2_hidden(C_79,A_81)
      | k1_xboole_0 != B_80 ) ),
    inference(resolution,[status(thm)],[c_194,c_2])).

tff(c_636,plain,(
    ! [A_136,C_137,A_138] :
      ( ~ r2_hidden('#skF_6'(A_136,k3_tarski(A_136),C_137),A_138)
      | k1_xboole_0 != A_136
      | ~ r2_hidden(C_137,k3_tarski(A_136)) ) ),
    inference(resolution,[status(thm)],[c_20,c_231])).

tff(c_652,plain,(
    ! [A_139,C_140] :
      ( k1_xboole_0 != A_139
      | ~ r2_hidden(C_140,k3_tarski(A_139)) ) ),
    inference(resolution,[status(thm)],[c_20,c_636])).

tff(c_692,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_652])).

tff(c_36,plain,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_695,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_692,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:53:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.27/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.50  
% 3.27/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.51  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_6 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 3.27/1.51  
% 3.27/1.51  %Foreground sorts:
% 3.27/1.51  
% 3.27/1.51  
% 3.27/1.51  %Background operators:
% 3.27/1.51  
% 3.27/1.51  
% 3.27/1.51  %Foreground operators:
% 3.27/1.51  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.27/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.27/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.27/1.51  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.27/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.27/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.27/1.51  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.27/1.51  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.27/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.27/1.51  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.27/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.27/1.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.27/1.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.27/1.51  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.27/1.51  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.27/1.51  
% 3.27/1.52  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.27/1.52  tff(f_69, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 3.27/1.52  tff(f_53, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.27/1.52  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.27/1.52  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.27/1.52  tff(f_59, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.27/1.52  tff(f_71, negated_conjecture, ~(k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 3.27/1.52  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.27/1.52  tff(c_20, plain, (![A_13, C_28]: (r2_hidden('#skF_6'(A_13, k3_tarski(A_13), C_28), A_13) | ~r2_hidden(C_28, k3_tarski(A_13)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.27/1.52  tff(c_10, plain, (![A_8]: (k2_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.27/1.52  tff(c_46, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k2_xboole_0(A_33, B_34))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.27/1.52  tff(c_53, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_46])).
% 3.27/1.52  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.27/1.52  tff(c_16, plain, (![A_11, B_12]: (r1_xboole_0(A_11, B_12) | k4_xboole_0(A_11, B_12)!=A_11)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.27/1.52  tff(c_72, plain, (![A_45, B_46, C_47]: (~r1_xboole_0(A_45, B_46) | ~r2_hidden(C_47, B_46) | ~r2_hidden(C_47, A_45))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.27/1.52  tff(c_86, plain, (![C_51, B_52, A_53]: (~r2_hidden(C_51, B_52) | ~r2_hidden(C_51, A_53) | k4_xboole_0(A_53, B_52)!=A_53)), inference(resolution, [status(thm)], [c_16, c_72])).
% 3.27/1.52  tff(c_167, plain, (![A_68, B_69, A_70]: (~r2_hidden('#skF_1'(A_68, B_69), A_70) | k4_xboole_0(A_70, B_69)!=A_70 | r1_xboole_0(A_68, B_69))), inference(resolution, [status(thm)], [c_4, c_86])).
% 3.27/1.52  tff(c_178, plain, (![B_2, A_1]: (k4_xboole_0(B_2, B_2)!=B_2 | r1_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_4, c_167])).
% 3.27/1.52  tff(c_194, plain, (![B_73, A_74]: (k1_xboole_0!=B_73 | r1_xboole_0(A_74, B_73))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_178])).
% 3.27/1.52  tff(c_2, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.27/1.52  tff(c_231, plain, (![C_79, B_80, A_81]: (~r2_hidden(C_79, B_80) | ~r2_hidden(C_79, A_81) | k1_xboole_0!=B_80)), inference(resolution, [status(thm)], [c_194, c_2])).
% 3.27/1.52  tff(c_636, plain, (![A_136, C_137, A_138]: (~r2_hidden('#skF_6'(A_136, k3_tarski(A_136), C_137), A_138) | k1_xboole_0!=A_136 | ~r2_hidden(C_137, k3_tarski(A_136)))), inference(resolution, [status(thm)], [c_20, c_231])).
% 3.27/1.52  tff(c_652, plain, (![A_139, C_140]: (k1_xboole_0!=A_139 | ~r2_hidden(C_140, k3_tarski(A_139)))), inference(resolution, [status(thm)], [c_20, c_636])).
% 3.27/1.52  tff(c_692, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_652])).
% 3.27/1.52  tff(c_36, plain, (k3_tarski(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.27/1.52  tff(c_695, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_692, c_36])).
% 3.27/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.52  
% 3.27/1.52  Inference rules
% 3.27/1.52  ----------------------
% 3.27/1.52  #Ref     : 0
% 3.27/1.52  #Sup     : 161
% 3.27/1.52  #Fact    : 0
% 3.27/1.52  #Define  : 0
% 3.27/1.52  #Split   : 0
% 3.27/1.52  #Chain   : 0
% 3.27/1.52  #Close   : 0
% 3.27/1.52  
% 3.27/1.52  Ordering : KBO
% 3.27/1.52  
% 3.27/1.52  Simplification rules
% 3.27/1.52  ----------------------
% 3.27/1.52  #Subsume      : 25
% 3.27/1.52  #Demod        : 8
% 3.27/1.52  #Tautology    : 26
% 3.27/1.52  #SimpNegUnit  : 0
% 3.27/1.52  #BackRed      : 1
% 3.27/1.52  
% 3.27/1.52  #Partial instantiations: 0
% 3.27/1.52  #Strategies tried      : 1
% 3.27/1.52  
% 3.27/1.52  Timing (in seconds)
% 3.27/1.52  ----------------------
% 3.27/1.52  Preprocessing        : 0.29
% 3.27/1.52  Parsing              : 0.16
% 3.27/1.52  CNF conversion       : 0.02
% 3.27/1.52  Main loop            : 0.44
% 3.27/1.52  Inferencing          : 0.17
% 3.27/1.52  Reduction            : 0.10
% 3.27/1.52  Demodulation         : 0.07
% 3.27/1.52  BG Simplification    : 0.02
% 3.27/1.52  Subsumption          : 0.11
% 3.27/1.52  Abstraction          : 0.03
% 3.27/1.52  MUC search           : 0.00
% 3.27/1.52  Cooper               : 0.00
% 3.27/1.52  Total                : 0.76
% 3.27/1.52  Index Insertion      : 0.00
% 3.27/1.52  Index Deletion       : 0.00
% 3.27/1.52  Index Matching       : 0.00
% 3.27/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
