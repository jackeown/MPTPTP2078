%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:12 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   46 (  49 expanded)
%              Number of leaves         :   28 (  30 expanded)
%              Depth                    :    5
%              Number of atoms          :   42 (  46 expanded)
%              Number of equality atoms :   17 (  18 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_45,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_92,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
          & A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_57,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_74,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_76,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_10,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_132,plain,(
    ! [A_67,B_68] :
      ( k3_xboole_0(A_67,B_68) = k1_xboole_0
      | ~ r1_xboole_0(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_140,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_132])).

tff(c_154,plain,(
    ! [A_70,B_71,C_72] :
      ( ~ r1_xboole_0(A_70,B_71)
      | ~ r2_hidden(C_72,k3_xboole_0(A_70,B_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_157,plain,(
    ! [A_8,C_72] :
      ( ~ r1_xboole_0(A_8,k1_xboole_0)
      | ~ r2_hidden(C_72,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_154])).

tff(c_159,plain,(
    ! [C_72] : ~ r2_hidden(C_72,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_157])).

tff(c_54,plain,(
    '#skF_5' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_56,plain,(
    r1_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_57,plain,(
    r1_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56])).

tff(c_64,plain,(
    ! [A_46] :
      ( ~ r1_xboole_0(A_46,A_46)
      | k1_xboole_0 = A_46 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_72,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_57,c_64])).

tff(c_40,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_93,plain,(
    ! [A_57,B_58] : k1_enumset1(A_57,A_57,B_58) = k2_tarski(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_22,plain,(
    ! [E_16,B_11,C_12] : r2_hidden(E_16,k1_enumset1(E_16,B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_111,plain,(
    ! [A_59,B_60] : r2_hidden(A_59,k2_tarski(A_59,B_60)) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_22])).

tff(c_115,plain,(
    ! [A_61] : r2_hidden(A_61,k1_tarski(A_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_111])).

tff(c_118,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_115])).

tff(c_161,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_159,c_118])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:11:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.35/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.39  
% 2.35/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.39  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.35/1.39  
% 2.35/1.39  %Foreground sorts:
% 2.35/1.39  
% 2.35/1.39  
% 2.35/1.39  %Background operators:
% 2.35/1.39  
% 2.35/1.39  
% 2.35/1.39  %Foreground operators:
% 2.35/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.35/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.35/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.35/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.35/1.39  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.35/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.35/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.35/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.35/1.39  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.35/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.35/1.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.35/1.39  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.35/1.39  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.35/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.35/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.35/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.35/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.35/1.39  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.35/1.39  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.35/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.35/1.39  
% 2.35/1.40  tff(f_45, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.35/1.40  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.35/1.40  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.35/1.40  tff(f_92, negated_conjecture, ~(![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 2.35/1.40  tff(f_57, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.35/1.40  tff(f_74, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.35/1.40  tff(f_76, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.35/1.40  tff(f_72, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.35/1.40  tff(c_10, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.35/1.40  tff(c_132, plain, (![A_67, B_68]: (k3_xboole_0(A_67, B_68)=k1_xboole_0 | ~r1_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.35/1.40  tff(c_140, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_132])).
% 2.35/1.40  tff(c_154, plain, (![A_70, B_71, C_72]: (~r1_xboole_0(A_70, B_71) | ~r2_hidden(C_72, k3_xboole_0(A_70, B_71)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.35/1.40  tff(c_157, plain, (![A_8, C_72]: (~r1_xboole_0(A_8, k1_xboole_0) | ~r2_hidden(C_72, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_140, c_154])).
% 2.35/1.40  tff(c_159, plain, (![C_72]: (~r2_hidden(C_72, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_157])).
% 2.35/1.40  tff(c_54, plain, ('#skF_5'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.35/1.40  tff(c_56, plain, (r1_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.35/1.40  tff(c_57, plain, (r1_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_56])).
% 2.35/1.40  tff(c_64, plain, (![A_46]: (~r1_xboole_0(A_46, A_46) | k1_xboole_0=A_46)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.35/1.40  tff(c_72, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_57, c_64])).
% 2.35/1.40  tff(c_40, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.35/1.40  tff(c_93, plain, (![A_57, B_58]: (k1_enumset1(A_57, A_57, B_58)=k2_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.35/1.40  tff(c_22, plain, (![E_16, B_11, C_12]: (r2_hidden(E_16, k1_enumset1(E_16, B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.35/1.40  tff(c_111, plain, (![A_59, B_60]: (r2_hidden(A_59, k2_tarski(A_59, B_60)))), inference(superposition, [status(thm), theory('equality')], [c_93, c_22])).
% 2.35/1.40  tff(c_115, plain, (![A_61]: (r2_hidden(A_61, k1_tarski(A_61)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_111])).
% 2.35/1.40  tff(c_118, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_72, c_115])).
% 2.35/1.40  tff(c_161, plain, $false, inference(negUnitSimplification, [status(thm)], [c_159, c_118])).
% 2.35/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.40  
% 2.35/1.40  Inference rules
% 2.35/1.40  ----------------------
% 2.35/1.40  #Ref     : 0
% 2.35/1.40  #Sup     : 23
% 2.35/1.40  #Fact    : 0
% 2.35/1.40  #Define  : 0
% 2.35/1.40  #Split   : 0
% 2.35/1.40  #Chain   : 0
% 2.35/1.40  #Close   : 0
% 2.35/1.40  
% 2.35/1.40  Ordering : KBO
% 2.35/1.40  
% 2.35/1.40  Simplification rules
% 2.35/1.40  ----------------------
% 2.35/1.40  #Subsume      : 0
% 2.35/1.40  #Demod        : 8
% 2.35/1.40  #Tautology    : 17
% 2.35/1.40  #SimpNegUnit  : 1
% 2.35/1.40  #BackRed      : 2
% 2.35/1.40  
% 2.35/1.40  #Partial instantiations: 0
% 2.35/1.40  #Strategies tried      : 1
% 2.35/1.40  
% 2.35/1.40  Timing (in seconds)
% 2.35/1.40  ----------------------
% 2.35/1.40  Preprocessing        : 0.41
% 2.35/1.40  Parsing              : 0.18
% 2.35/1.41  CNF conversion       : 0.04
% 2.35/1.41  Main loop            : 0.14
% 2.35/1.41  Inferencing          : 0.04
% 2.35/1.41  Reduction            : 0.05
% 2.35/1.41  Demodulation         : 0.04
% 2.35/1.41  BG Simplification    : 0.03
% 2.35/1.41  Subsumption          : 0.03
% 2.35/1.41  Abstraction          : 0.01
% 2.35/1.41  MUC search           : 0.00
% 2.35/1.41  Cooper               : 0.00
% 2.35/1.41  Total                : 0.59
% 2.35/1.41  Index Insertion      : 0.00
% 2.35/1.41  Index Deletion       : 0.00
% 2.35/1.41  Index Matching       : 0.00
% 2.35/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
