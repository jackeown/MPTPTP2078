%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:55 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   43 (  60 expanded)
%              Number of leaves         :   24 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   38 (  62 expanded)
%              Number of equality atoms :   28 (  48 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_zfmisc_1)).

tff(f_48,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_50,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(c_44,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_30,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_106,plain,(
    ! [A_63,B_64,C_65] : k2_xboole_0(k1_tarski(A_63),k2_tarski(B_64,C_65)) = k1_enumset1(A_63,B_64,C_65) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_127,plain,(
    ! [A_70,A_71] : k2_xboole_0(k1_tarski(A_70),k1_tarski(A_71)) = k1_enumset1(A_70,A_71,A_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_106])).

tff(c_46,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_59,plain,(
    ! [A_51,B_52] :
      ( k2_xboole_0(A_51,B_52) = B_52
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_63,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_59])).

tff(c_136,plain,(
    k1_enumset1('#skF_3','#skF_4','#skF_4') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_63])).

tff(c_10,plain,(
    ! [E_9,B_4,C_5] : r2_hidden(E_9,k1_enumset1(E_9,B_4,C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_178,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_10])).

tff(c_32,plain,(
    ! [A_14,B_15] : k1_enumset1(A_14,A_14,B_15) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_162,plain,(
    ! [B_15] : k2_xboole_0(k1_tarski(B_15),k1_tarski(B_15)) = k2_tarski(B_15,B_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_127])).

tff(c_194,plain,(
    ! [B_74] : k2_xboole_0(k1_tarski(B_74),k1_tarski(B_74)) = k1_tarski(B_74) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_162])).

tff(c_115,plain,(
    ! [A_63,A_13] : k2_xboole_0(k1_tarski(A_63),k1_tarski(A_13)) = k1_enumset1(A_63,A_13,A_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_106])).

tff(c_203,plain,(
    ! [B_74] : k1_enumset1(B_74,B_74,B_74) = k1_tarski(B_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_115])).

tff(c_267,plain,(
    ! [E_78,C_79,B_80,A_81] :
      ( E_78 = C_79
      | E_78 = B_80
      | E_78 = A_81
      | ~ r2_hidden(E_78,k1_enumset1(A_81,B_80,C_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_322,plain,(
    ! [E_88,B_89] :
      ( E_88 = B_89
      | E_88 = B_89
      | E_88 = B_89
      | ~ r2_hidden(E_88,k1_tarski(B_89)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_267])).

tff(c_325,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_178,c_322])).

tff(c_332,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_44,c_44,c_325])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:25:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.57/1.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.68  
% 2.57/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.68  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.68/1.68  
% 2.68/1.68  %Foreground sorts:
% 2.68/1.68  
% 2.68/1.68  
% 2.68/1.68  %Background operators:
% 2.68/1.68  
% 2.68/1.68  
% 2.68/1.68  %Foreground operators:
% 2.68/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.68/1.68  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.68/1.68  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.68/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.68/1.68  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.68/1.68  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.68/1.68  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.68/1.68  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.68/1.68  tff('#skF_3', type, '#skF_3': $i).
% 2.68/1.68  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.68/1.68  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.68/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.68  tff('#skF_4', type, '#skF_4': $i).
% 2.68/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.68  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.68/1.68  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.68/1.68  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.68/1.68  
% 2.68/1.70  tff(f_65, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_zfmisc_1)).
% 2.68/1.70  tff(f_48, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.68/1.70  tff(f_46, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 2.68/1.70  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.68/1.70  tff(f_44, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.68/1.70  tff(f_50, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.68/1.70  tff(c_44, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.68/1.70  tff(c_30, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.68/1.70  tff(c_106, plain, (![A_63, B_64, C_65]: (k2_xboole_0(k1_tarski(A_63), k2_tarski(B_64, C_65))=k1_enumset1(A_63, B_64, C_65))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.68/1.70  tff(c_127, plain, (![A_70, A_71]: (k2_xboole_0(k1_tarski(A_70), k1_tarski(A_71))=k1_enumset1(A_70, A_71, A_71))), inference(superposition, [status(thm), theory('equality')], [c_30, c_106])).
% 2.68/1.70  tff(c_46, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.68/1.70  tff(c_59, plain, (![A_51, B_52]: (k2_xboole_0(A_51, B_52)=B_52 | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.68/1.70  tff(c_63, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_4')), inference(resolution, [status(thm)], [c_46, c_59])).
% 2.68/1.70  tff(c_136, plain, (k1_enumset1('#skF_3', '#skF_4', '#skF_4')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_127, c_63])).
% 2.68/1.70  tff(c_10, plain, (![E_9, B_4, C_5]: (r2_hidden(E_9, k1_enumset1(E_9, B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.68/1.70  tff(c_178, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_136, c_10])).
% 2.68/1.70  tff(c_32, plain, (![A_14, B_15]: (k1_enumset1(A_14, A_14, B_15)=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.68/1.70  tff(c_162, plain, (![B_15]: (k2_xboole_0(k1_tarski(B_15), k1_tarski(B_15))=k2_tarski(B_15, B_15))), inference(superposition, [status(thm), theory('equality')], [c_32, c_127])).
% 2.68/1.70  tff(c_194, plain, (![B_74]: (k2_xboole_0(k1_tarski(B_74), k1_tarski(B_74))=k1_tarski(B_74))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_162])).
% 2.68/1.70  tff(c_115, plain, (![A_63, A_13]: (k2_xboole_0(k1_tarski(A_63), k1_tarski(A_13))=k1_enumset1(A_63, A_13, A_13))), inference(superposition, [status(thm), theory('equality')], [c_30, c_106])).
% 2.68/1.70  tff(c_203, plain, (![B_74]: (k1_enumset1(B_74, B_74, B_74)=k1_tarski(B_74))), inference(superposition, [status(thm), theory('equality')], [c_194, c_115])).
% 2.68/1.70  tff(c_267, plain, (![E_78, C_79, B_80, A_81]: (E_78=C_79 | E_78=B_80 | E_78=A_81 | ~r2_hidden(E_78, k1_enumset1(A_81, B_80, C_79)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.68/1.70  tff(c_322, plain, (![E_88, B_89]: (E_88=B_89 | E_88=B_89 | E_88=B_89 | ~r2_hidden(E_88, k1_tarski(B_89)))), inference(superposition, [status(thm), theory('equality')], [c_203, c_267])).
% 2.68/1.70  tff(c_325, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_178, c_322])).
% 2.68/1.70  tff(c_332, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_44, c_44, c_325])).
% 2.68/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.70  
% 2.68/1.70  Inference rules
% 2.68/1.70  ----------------------
% 2.68/1.70  #Ref     : 0
% 2.68/1.70  #Sup     : 67
% 2.68/1.70  #Fact    : 0
% 2.68/1.70  #Define  : 0
% 2.68/1.70  #Split   : 0
% 2.68/1.70  #Chain   : 0
% 2.68/1.70  #Close   : 0
% 2.68/1.70  
% 2.68/1.70  Ordering : KBO
% 2.68/1.70  
% 2.68/1.70  Simplification rules
% 2.68/1.70  ----------------------
% 2.68/1.70  #Subsume      : 0
% 2.68/1.70  #Demod        : 23
% 2.68/1.70  #Tautology    : 50
% 2.68/1.70  #SimpNegUnit  : 3
% 2.68/1.70  #BackRed      : 0
% 2.68/1.70  
% 2.68/1.70  #Partial instantiations: 0
% 2.68/1.70  #Strategies tried      : 1
% 2.68/1.70  
% 2.68/1.70  Timing (in seconds)
% 2.68/1.70  ----------------------
% 2.68/1.70  Preprocessing        : 0.51
% 2.68/1.71  Parsing              : 0.25
% 2.68/1.71  CNF conversion       : 0.04
% 2.68/1.71  Main loop            : 0.31
% 2.68/1.71  Inferencing          : 0.11
% 2.68/1.71  Reduction            : 0.10
% 2.68/1.71  Demodulation         : 0.08
% 2.68/1.71  BG Simplification    : 0.02
% 2.68/1.71  Subsumption          : 0.05
% 2.68/1.71  Abstraction          : 0.02
% 2.68/1.71  MUC search           : 0.00
% 2.68/1.71  Cooper               : 0.00
% 2.68/1.71  Total                : 0.86
% 2.68/1.71  Index Insertion      : 0.00
% 2.68/1.71  Index Deletion       : 0.00
% 2.68/1.71  Index Matching       : 0.00
% 2.68/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
