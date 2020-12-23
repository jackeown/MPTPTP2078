%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:22 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   52 (  52 expanded)
%              Number of leaves         :   35 (  35 expanded)
%              Depth                    :    6
%              Number of atoms          :   34 (  34 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_3

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_36,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_62,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_115,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_72,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_99,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_101,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_97,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_10,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_22,plain,(
    ! [A_18] : k3_xboole_0(A_18,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_76,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_32,plain,(
    ! [A_25,B_26] : r1_tarski(A_25,k2_xboole_0(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_109,plain,(
    r1_tarski(k1_tarski('#skF_5'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_32])).

tff(c_255,plain,(
    ! [A_100,B_101] :
      ( k3_xboole_0(A_100,B_101) = A_100
      | ~ r1_tarski(A_100,B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_261,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k1_xboole_0) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_109,c_255])).

tff(c_267,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_261])).

tff(c_62,plain,(
    ! [A_38] : k2_tarski(A_38,A_38) = k1_tarski(A_38) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_421,plain,(
    ! [A_112,B_113] : k1_enumset1(A_112,A_112,B_113) = k2_tarski(A_112,B_113) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_156,plain,(
    ! [E_76,B_77,C_78] : r2_hidden(E_76,k1_enumset1(E_76,B_77,C_78)) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_160,plain,(
    ! [E_76,B_77,C_78] : ~ v1_xboole_0(k1_enumset1(E_76,B_77,C_78)) ),
    inference(resolution,[status(thm)],[c_156,c_2])).

tff(c_441,plain,(
    ! [A_114,B_115] : ~ v1_xboole_0(k2_tarski(A_114,B_115)) ),
    inference(superposition,[status(thm),theory(equality)],[c_421,c_160])).

tff(c_448,plain,(
    ! [A_116] : ~ v1_xboole_0(k1_tarski(A_116)) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_441])).

tff(c_450,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_448])).

tff(c_453,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_450])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:42:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.33  
% 2.56/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.33  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_3
% 2.56/1.33  
% 2.56/1.33  %Foreground sorts:
% 2.56/1.33  
% 2.56/1.33  
% 2.56/1.33  %Background operators:
% 2.56/1.33  
% 2.56/1.33  
% 2.56/1.33  %Foreground operators:
% 2.56/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.56/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.56/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.56/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.56/1.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.56/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.56/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.56/1.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.56/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.56/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.56/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.56/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.56/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.56/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.56/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.56/1.33  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.56/1.33  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.56/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.56/1.33  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.56/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.56/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.56/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.56/1.33  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.56/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.56/1.33  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.56/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.56/1.33  
% 2.56/1.34  tff(f_36, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.56/1.34  tff(f_62, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.56/1.34  tff(f_115, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.56/1.34  tff(f_72, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.56/1.34  tff(f_60, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.56/1.34  tff(f_99, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.56/1.34  tff(f_101, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.56/1.34  tff(f_97, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.56/1.34  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.56/1.34  tff(c_10, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.56/1.34  tff(c_22, plain, (![A_18]: (k3_xboole_0(A_18, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.56/1.34  tff(c_76, plain, (k2_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.56/1.34  tff(c_32, plain, (![A_25, B_26]: (r1_tarski(A_25, k2_xboole_0(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.56/1.34  tff(c_109, plain, (r1_tarski(k1_tarski('#skF_5'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_76, c_32])).
% 2.56/1.34  tff(c_255, plain, (![A_100, B_101]: (k3_xboole_0(A_100, B_101)=A_100 | ~r1_tarski(A_100, B_101))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.56/1.34  tff(c_261, plain, (k3_xboole_0(k1_tarski('#skF_5'), k1_xboole_0)=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_109, c_255])).
% 2.56/1.34  tff(c_267, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_22, c_261])).
% 2.56/1.34  tff(c_62, plain, (![A_38]: (k2_tarski(A_38, A_38)=k1_tarski(A_38))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.56/1.34  tff(c_421, plain, (![A_112, B_113]: (k1_enumset1(A_112, A_112, B_113)=k2_tarski(A_112, B_113))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.56/1.34  tff(c_156, plain, (![E_76, B_77, C_78]: (r2_hidden(E_76, k1_enumset1(E_76, B_77, C_78)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.56/1.34  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.56/1.34  tff(c_160, plain, (![E_76, B_77, C_78]: (~v1_xboole_0(k1_enumset1(E_76, B_77, C_78)))), inference(resolution, [status(thm)], [c_156, c_2])).
% 2.56/1.34  tff(c_441, plain, (![A_114, B_115]: (~v1_xboole_0(k2_tarski(A_114, B_115)))), inference(superposition, [status(thm), theory('equality')], [c_421, c_160])).
% 2.56/1.34  tff(c_448, plain, (![A_116]: (~v1_xboole_0(k1_tarski(A_116)))), inference(superposition, [status(thm), theory('equality')], [c_62, c_441])).
% 2.56/1.34  tff(c_450, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_267, c_448])).
% 2.56/1.34  tff(c_453, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_450])).
% 2.56/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.34  
% 2.56/1.34  Inference rules
% 2.56/1.34  ----------------------
% 2.56/1.34  #Ref     : 0
% 2.56/1.34  #Sup     : 96
% 2.56/1.34  #Fact    : 0
% 2.56/1.34  #Define  : 0
% 2.56/1.34  #Split   : 0
% 2.56/1.34  #Chain   : 0
% 2.56/1.34  #Close   : 0
% 2.56/1.34  
% 2.56/1.34  Ordering : KBO
% 2.56/1.34  
% 2.56/1.34  Simplification rules
% 2.56/1.34  ----------------------
% 2.56/1.34  #Subsume      : 4
% 2.56/1.34  #Demod        : 16
% 2.56/1.34  #Tautology    : 67
% 2.56/1.34  #SimpNegUnit  : 0
% 2.56/1.34  #BackRed      : 2
% 2.56/1.34  
% 2.56/1.34  #Partial instantiations: 0
% 2.56/1.34  #Strategies tried      : 1
% 2.56/1.34  
% 2.56/1.34  Timing (in seconds)
% 2.56/1.34  ----------------------
% 2.56/1.34  Preprocessing        : 0.36
% 2.56/1.34  Parsing              : 0.19
% 2.56/1.34  CNF conversion       : 0.03
% 2.56/1.34  Main loop            : 0.22
% 2.56/1.34  Inferencing          : 0.08
% 2.56/1.34  Reduction            : 0.07
% 2.56/1.34  Demodulation         : 0.06
% 2.56/1.34  BG Simplification    : 0.02
% 2.56/1.34  Subsumption          : 0.04
% 2.56/1.34  Abstraction          : 0.01
% 2.56/1.34  MUC search           : 0.00
% 2.56/1.35  Cooper               : 0.00
% 2.56/1.35  Total                : 0.60
% 2.56/1.35  Index Insertion      : 0.00
% 2.56/1.35  Index Deletion       : 0.00
% 2.56/1.35  Index Matching       : 0.00
% 2.56/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
