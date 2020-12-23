%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:58 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :   43 (  68 expanded)
%              Number of leaves         :   23 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   46 (  90 expanded)
%              Number of equality atoms :   17 (  32 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_5 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_52,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_32,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_34,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_326,plain,(
    ! [A_100,B_101] :
      ( r2_hidden(k4_tarski('#skF_2'(A_100,B_101),'#skF_3'(A_100,B_101)),A_100)
      | r2_hidden('#skF_4'(A_100,B_101),B_101)
      | k1_relat_1(A_100) = B_101 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_621,plain,(
    ! [A_133,B_134] :
      ( ~ v1_xboole_0(A_133)
      | r2_hidden('#skF_4'(A_133,B_134),B_134)
      | k1_relat_1(A_133) = B_134 ) ),
    inference(resolution,[status(thm)],[c_326,c_2])).

tff(c_721,plain,(
    ! [B_135,A_136] :
      ( ~ v1_xboole_0(B_135)
      | ~ v1_xboole_0(A_136)
      | k1_relat_1(A_136) = B_135 ) ),
    inference(resolution,[status(thm)],[c_621,c_2])).

tff(c_782,plain,(
    ! [A_137] :
      ( ~ v1_xboole_0(A_137)
      | k1_relat_1(A_137) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_721])).

tff(c_842,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_782])).

tff(c_865,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_842])).

tff(c_866,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_1240,plain,(
    ! [A_189,B_190] :
      ( r2_hidden(k4_tarski('#skF_7'(A_189,B_190),'#skF_6'(A_189,B_190)),A_189)
      | r2_hidden('#skF_8'(A_189,B_190),B_190)
      | k2_relat_1(A_189) = B_190 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_867,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_880,plain,(
    ! [C_147,A_148] :
      ( r2_hidden(k4_tarski(C_147,'#skF_5'(A_148,k1_relat_1(A_148),C_147)),A_148)
      | ~ r2_hidden(C_147,k1_relat_1(A_148)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_910,plain,(
    ! [A_151,C_152] :
      ( ~ v1_xboole_0(A_151)
      | ~ r2_hidden(C_152,k1_relat_1(A_151)) ) ),
    inference(resolution,[status(thm)],[c_880,c_2])).

tff(c_925,plain,(
    ! [C_152] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(C_152,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_867,c_910])).

tff(c_930,plain,(
    ! [C_152] : ~ r2_hidden(C_152,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_925])).

tff(c_1385,plain,(
    ! [B_193] :
      ( r2_hidden('#skF_8'(k1_xboole_0,B_193),B_193)
      | k2_relat_1(k1_xboole_0) = B_193 ) ),
    inference(resolution,[status(thm)],[c_1240,c_930])).

tff(c_1461,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1385,c_930])).

tff(c_1491,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_866,c_1461])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:30:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.14/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.47  
% 3.14/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.48  %$ r2_hidden > v1_xboole_0 > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_5 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_4
% 3.14/1.48  
% 3.14/1.48  %Foreground sorts:
% 3.14/1.48  
% 3.14/1.48  
% 3.14/1.48  %Background operators:
% 3.14/1.48  
% 3.14/1.48  
% 3.14/1.48  %Foreground operators:
% 3.14/1.48  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.14/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.14/1.48  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.14/1.48  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.14/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.14/1.48  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.14/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.14/1.48  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.14/1.48  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 3.14/1.48  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 3.14/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.48  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.14/1.48  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.14/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.14/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.14/1.48  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.14/1.48  
% 3.14/1.49  tff(f_52, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.14/1.49  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.14/1.49  tff(f_40, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 3.14/1.49  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.14/1.49  tff(f_48, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 3.14/1.49  tff(c_32, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.14/1.49  tff(c_34, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_32])).
% 3.14/1.49  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.14/1.49  tff(c_326, plain, (![A_100, B_101]: (r2_hidden(k4_tarski('#skF_2'(A_100, B_101), '#skF_3'(A_100, B_101)), A_100) | r2_hidden('#skF_4'(A_100, B_101), B_101) | k1_relat_1(A_100)=B_101)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.14/1.49  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.14/1.49  tff(c_621, plain, (![A_133, B_134]: (~v1_xboole_0(A_133) | r2_hidden('#skF_4'(A_133, B_134), B_134) | k1_relat_1(A_133)=B_134)), inference(resolution, [status(thm)], [c_326, c_2])).
% 3.14/1.49  tff(c_721, plain, (![B_135, A_136]: (~v1_xboole_0(B_135) | ~v1_xboole_0(A_136) | k1_relat_1(A_136)=B_135)), inference(resolution, [status(thm)], [c_621, c_2])).
% 3.14/1.49  tff(c_782, plain, (![A_137]: (~v1_xboole_0(A_137) | k1_relat_1(A_137)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_721])).
% 3.14/1.49  tff(c_842, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_782])).
% 3.14/1.49  tff(c_865, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_842])).
% 3.14/1.49  tff(c_866, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 3.14/1.49  tff(c_1240, plain, (![A_189, B_190]: (r2_hidden(k4_tarski('#skF_7'(A_189, B_190), '#skF_6'(A_189, B_190)), A_189) | r2_hidden('#skF_8'(A_189, B_190), B_190) | k2_relat_1(A_189)=B_190)), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.14/1.49  tff(c_867, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 3.14/1.49  tff(c_880, plain, (![C_147, A_148]: (r2_hidden(k4_tarski(C_147, '#skF_5'(A_148, k1_relat_1(A_148), C_147)), A_148) | ~r2_hidden(C_147, k1_relat_1(A_148)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.14/1.49  tff(c_910, plain, (![A_151, C_152]: (~v1_xboole_0(A_151) | ~r2_hidden(C_152, k1_relat_1(A_151)))), inference(resolution, [status(thm)], [c_880, c_2])).
% 3.14/1.49  tff(c_925, plain, (![C_152]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(C_152, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_867, c_910])).
% 3.14/1.49  tff(c_930, plain, (![C_152]: (~r2_hidden(C_152, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_925])).
% 3.14/1.49  tff(c_1385, plain, (![B_193]: (r2_hidden('#skF_8'(k1_xboole_0, B_193), B_193) | k2_relat_1(k1_xboole_0)=B_193)), inference(resolution, [status(thm)], [c_1240, c_930])).
% 3.14/1.49  tff(c_1461, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_1385, c_930])).
% 3.14/1.49  tff(c_1491, plain, $false, inference(negUnitSimplification, [status(thm)], [c_866, c_1461])).
% 3.14/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.49  
% 3.14/1.49  Inference rules
% 3.14/1.49  ----------------------
% 3.14/1.49  #Ref     : 0
% 3.14/1.49  #Sup     : 290
% 3.14/1.49  #Fact    : 0
% 3.14/1.49  #Define  : 0
% 3.14/1.49  #Split   : 1
% 3.14/1.49  #Chain   : 0
% 3.14/1.49  #Close   : 0
% 3.14/1.49  
% 3.14/1.49  Ordering : KBO
% 3.14/1.49  
% 3.14/1.49  Simplification rules
% 3.14/1.49  ----------------------
% 3.14/1.49  #Subsume      : 4
% 3.14/1.49  #Demod        : 14
% 3.14/1.49  #Tautology    : 13
% 3.14/1.49  #SimpNegUnit  : 3
% 3.14/1.49  #BackRed      : 0
% 3.14/1.49  
% 3.14/1.49  #Partial instantiations: 0
% 3.14/1.49  #Strategies tried      : 1
% 3.14/1.49  
% 3.14/1.49  Timing (in seconds)
% 3.14/1.49  ----------------------
% 3.34/1.49  Preprocessing        : 0.27
% 3.34/1.49  Parsing              : 0.14
% 3.34/1.49  CNF conversion       : 0.02
% 3.34/1.49  Main loop            : 0.47
% 3.34/1.49  Inferencing          : 0.18
% 3.34/1.49  Reduction            : 0.09
% 3.34/1.49  Demodulation         : 0.05
% 3.34/1.49  BG Simplification    : 0.02
% 3.34/1.49  Subsumption          : 0.14
% 3.34/1.49  Abstraction          : 0.02
% 3.34/1.49  MUC search           : 0.00
% 3.34/1.49  Cooper               : 0.00
% 3.34/1.49  Total                : 0.76
% 3.34/1.49  Index Insertion      : 0.00
% 3.34/1.49  Index Deletion       : 0.00
% 3.34/1.49  Index Matching       : 0.00
% 3.34/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
