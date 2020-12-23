%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:51 EST 2020

% Result     : Theorem 3.82s
% Output     : CNFRefutation 3.93s
% Verified   : 
% Statistics : Number of formulae       :   42 (  45 expanded)
%              Number of leaves         :   28 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :   28 (  32 expanded)
%              Number of equality atoms :   22 (  26 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_2 > #skF_6 > #skF_3 > #skF_1 > #skF_5 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_91,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_95,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_89,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_90,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_82,plain,(
    ! [A_45] : k2_tarski(A_45,A_45) = k1_tarski(A_45) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_86,plain,(
    ! [A_48,B_49,C_50] : k2_enumset1(A_48,A_48,B_49,C_50) = k1_enumset1(A_48,B_49,C_50) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1891,plain,(
    ! [A_184,B_185,C_186,D_187] : k2_xboole_0(k2_tarski(A_184,B_185),k2_tarski(C_186,D_187)) = k2_enumset1(A_184,B_185,C_186,D_187) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1916,plain,(
    ! [A_45,C_186,D_187] : k2_xboole_0(k1_tarski(A_45),k2_tarski(C_186,D_187)) = k2_enumset1(A_45,A_45,C_186,D_187) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_1891])).

tff(c_2072,plain,(
    ! [A_200,C_201,D_202] : k2_xboole_0(k1_tarski(A_200),k2_tarski(C_201,D_202)) = k1_enumset1(A_200,C_201,D_202) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1916])).

tff(c_2096,plain,(
    ! [A_203,A_204] : k2_xboole_0(k1_tarski(A_203),k1_tarski(A_204)) = k1_enumset1(A_203,A_204,A_204) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_2072])).

tff(c_92,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2131,plain,(
    k1_enumset1('#skF_6','#skF_7','#skF_7') = k1_tarski('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2096,c_92])).

tff(c_48,plain,(
    ! [E_35,A_29,C_31] : r2_hidden(E_35,k1_enumset1(A_29,E_35,C_31)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2199,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2131,c_48])).

tff(c_68,plain,(
    ! [C_40,A_36] :
      ( C_40 = A_36
      | ~ r2_hidden(C_40,k1_tarski(A_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2222,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2199,c_68])).

tff(c_2227,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_2222])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:45:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.82/1.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.82/1.68  
% 3.82/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.82/1.68  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_2 > #skF_6 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 3.82/1.68  
% 3.82/1.68  %Foreground sorts:
% 3.82/1.68  
% 3.82/1.68  
% 3.82/1.68  %Background operators:
% 3.82/1.68  
% 3.82/1.68  
% 3.82/1.68  %Foreground operators:
% 3.82/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.82/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.82/1.68  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.82/1.68  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.82/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.82/1.68  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.82/1.68  tff('#skF_7', type, '#skF_7': $i).
% 3.82/1.68  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.82/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.82/1.68  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.82/1.68  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.82/1.68  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.82/1.68  tff('#skF_6', type, '#skF_6': $i).
% 3.82/1.68  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.82/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.82/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.82/1.68  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.82/1.68  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.82/1.68  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.82/1.68  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.82/1.68  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.82/1.68  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.82/1.68  
% 3.93/1.69  tff(f_102, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 3.93/1.69  tff(f_91, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.93/1.69  tff(f_95, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.93/1.69  tff(f_89, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 3.93/1.69  tff(f_80, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.93/1.69  tff(f_87, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.93/1.69  tff(c_90, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.93/1.69  tff(c_82, plain, (![A_45]: (k2_tarski(A_45, A_45)=k1_tarski(A_45))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.93/1.69  tff(c_86, plain, (![A_48, B_49, C_50]: (k2_enumset1(A_48, A_48, B_49, C_50)=k1_enumset1(A_48, B_49, C_50))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.93/1.69  tff(c_1891, plain, (![A_184, B_185, C_186, D_187]: (k2_xboole_0(k2_tarski(A_184, B_185), k2_tarski(C_186, D_187))=k2_enumset1(A_184, B_185, C_186, D_187))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.93/1.69  tff(c_1916, plain, (![A_45, C_186, D_187]: (k2_xboole_0(k1_tarski(A_45), k2_tarski(C_186, D_187))=k2_enumset1(A_45, A_45, C_186, D_187))), inference(superposition, [status(thm), theory('equality')], [c_82, c_1891])).
% 3.93/1.69  tff(c_2072, plain, (![A_200, C_201, D_202]: (k2_xboole_0(k1_tarski(A_200), k2_tarski(C_201, D_202))=k1_enumset1(A_200, C_201, D_202))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1916])).
% 3.93/1.69  tff(c_2096, plain, (![A_203, A_204]: (k2_xboole_0(k1_tarski(A_203), k1_tarski(A_204))=k1_enumset1(A_203, A_204, A_204))), inference(superposition, [status(thm), theory('equality')], [c_82, c_2072])).
% 3.93/1.69  tff(c_92, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.93/1.69  tff(c_2131, plain, (k1_enumset1('#skF_6', '#skF_7', '#skF_7')=k1_tarski('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2096, c_92])).
% 3.93/1.69  tff(c_48, plain, (![E_35, A_29, C_31]: (r2_hidden(E_35, k1_enumset1(A_29, E_35, C_31)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.93/1.69  tff(c_2199, plain, (r2_hidden('#skF_7', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2131, c_48])).
% 3.93/1.69  tff(c_68, plain, (![C_40, A_36]: (C_40=A_36 | ~r2_hidden(C_40, k1_tarski(A_36)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.93/1.69  tff(c_2222, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_2199, c_68])).
% 3.93/1.69  tff(c_2227, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_2222])).
% 3.93/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.93/1.69  
% 3.93/1.69  Inference rules
% 3.93/1.69  ----------------------
% 3.93/1.69  #Ref     : 0
% 3.93/1.69  #Sup     : 510
% 3.93/1.69  #Fact    : 0
% 3.93/1.69  #Define  : 0
% 3.93/1.69  #Split   : 0
% 3.93/1.69  #Chain   : 0
% 3.93/1.69  #Close   : 0
% 3.93/1.69  
% 3.93/1.69  Ordering : KBO
% 3.93/1.69  
% 3.93/1.69  Simplification rules
% 3.93/1.69  ----------------------
% 3.93/1.69  #Subsume      : 14
% 3.93/1.69  #Demod        : 286
% 3.93/1.69  #Tautology    : 306
% 3.93/1.69  #SimpNegUnit  : 1
% 3.93/1.69  #BackRed      : 4
% 3.93/1.69  
% 3.93/1.69  #Partial instantiations: 0
% 3.93/1.69  #Strategies tried      : 1
% 3.93/1.69  
% 3.93/1.69  Timing (in seconds)
% 3.93/1.69  ----------------------
% 3.93/1.69  Preprocessing        : 0.36
% 3.93/1.69  Parsing              : 0.18
% 3.93/1.69  CNF conversion       : 0.03
% 3.93/1.69  Main loop            : 0.54
% 3.93/1.69  Inferencing          : 0.19
% 3.93/1.69  Reduction            : 0.19
% 3.93/1.69  Demodulation         : 0.15
% 3.93/1.69  BG Simplification    : 0.03
% 3.93/1.69  Subsumption          : 0.09
% 3.93/1.69  Abstraction          : 0.03
% 3.93/1.69  MUC search           : 0.00
% 3.93/1.69  Cooper               : 0.00
% 3.93/1.69  Total                : 0.92
% 3.93/1.69  Index Insertion      : 0.00
% 3.93/1.69  Index Deletion       : 0.00
% 3.93/1.69  Index Matching       : 0.00
% 3.93/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
