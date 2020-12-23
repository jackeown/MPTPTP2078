%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:55 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   40 (  57 expanded)
%              Number of leaves         :   21 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :   38 (  62 expanded)
%              Number of equality atoms :   28 (  48 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_zfmisc_1)).

tff(f_50,axiom,(
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

tff(f_52,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(c_40,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_32,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_102,plain,(
    ! [A_49,B_50,C_51] : k2_xboole_0(k1_tarski(A_49),k2_tarski(B_50,C_51)) = k1_enumset1(A_49,B_50,C_51) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_123,plain,(
    ! [A_56,A_57] : k2_xboole_0(k1_tarski(A_56),k1_tarski(A_57)) = k1_enumset1(A_56,A_57,A_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_102])).

tff(c_42,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_55,plain,(
    ! [A_37,B_38] :
      ( k2_xboole_0(A_37,B_38) = B_38
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_59,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_55])).

tff(c_132,plain,(
    k1_enumset1('#skF_3','#skF_4','#skF_4') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_59])).

tff(c_10,plain,(
    ! [E_9,B_4,C_5] : r2_hidden(E_9,k1_enumset1(E_9,B_4,C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_174,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_10])).

tff(c_34,plain,(
    ! [A_18,B_19] : k1_enumset1(A_18,A_18,B_19) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_158,plain,(
    ! [B_19] : k2_xboole_0(k1_tarski(B_19),k1_tarski(B_19)) = k2_tarski(B_19,B_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_123])).

tff(c_190,plain,(
    ! [B_60] : k2_xboole_0(k1_tarski(B_60),k1_tarski(B_60)) = k1_tarski(B_60) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_158])).

tff(c_111,plain,(
    ! [A_49,A_17] : k2_xboole_0(k1_tarski(A_49),k1_tarski(A_17)) = k1_enumset1(A_49,A_17,A_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_102])).

tff(c_199,plain,(
    ! [B_60] : k1_enumset1(B_60,B_60,B_60) = k1_tarski(B_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_111])).

tff(c_263,plain,(
    ! [E_64,C_65,B_66,A_67] :
      ( E_64 = C_65
      | E_64 = B_66
      | E_64 = A_67
      | ~ r2_hidden(E_64,k1_enumset1(A_67,B_66,C_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_484,plain,(
    ! [E_84,B_85] :
      ( E_84 = B_85
      | E_84 = B_85
      | E_84 = B_85
      | ~ r2_hidden(E_84,k1_tarski(B_85)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_263])).

tff(c_487,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_174,c_484])).

tff(c_494,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_40,c_40,c_487])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:14:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.33/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.34  
% 2.33/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.34  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.33/1.34  
% 2.33/1.34  %Foreground sorts:
% 2.33/1.34  
% 2.33/1.34  
% 2.33/1.34  %Background operators:
% 2.33/1.34  
% 2.33/1.34  
% 2.33/1.34  %Foreground operators:
% 2.33/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.33/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.33/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.33/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.33/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.33/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.33/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.33/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.33/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.33/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.33/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.33/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.33/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.33/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.33/1.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.33/1.34  
% 2.33/1.35  tff(f_61, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_zfmisc_1)).
% 2.33/1.35  tff(f_50, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.33/1.35  tff(f_46, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 2.33/1.35  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.33/1.35  tff(f_44, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.33/1.35  tff(f_52, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.33/1.35  tff(c_40, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.33/1.35  tff(c_32, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.33/1.35  tff(c_102, plain, (![A_49, B_50, C_51]: (k2_xboole_0(k1_tarski(A_49), k2_tarski(B_50, C_51))=k1_enumset1(A_49, B_50, C_51))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.33/1.35  tff(c_123, plain, (![A_56, A_57]: (k2_xboole_0(k1_tarski(A_56), k1_tarski(A_57))=k1_enumset1(A_56, A_57, A_57))), inference(superposition, [status(thm), theory('equality')], [c_32, c_102])).
% 2.33/1.35  tff(c_42, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.33/1.35  tff(c_55, plain, (![A_37, B_38]: (k2_xboole_0(A_37, B_38)=B_38 | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.33/1.35  tff(c_59, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_4')), inference(resolution, [status(thm)], [c_42, c_55])).
% 2.33/1.35  tff(c_132, plain, (k1_enumset1('#skF_3', '#skF_4', '#skF_4')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_123, c_59])).
% 2.33/1.35  tff(c_10, plain, (![E_9, B_4, C_5]: (r2_hidden(E_9, k1_enumset1(E_9, B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.33/1.35  tff(c_174, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_132, c_10])).
% 2.33/1.35  tff(c_34, plain, (![A_18, B_19]: (k1_enumset1(A_18, A_18, B_19)=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.33/1.35  tff(c_158, plain, (![B_19]: (k2_xboole_0(k1_tarski(B_19), k1_tarski(B_19))=k2_tarski(B_19, B_19))), inference(superposition, [status(thm), theory('equality')], [c_34, c_123])).
% 2.33/1.35  tff(c_190, plain, (![B_60]: (k2_xboole_0(k1_tarski(B_60), k1_tarski(B_60))=k1_tarski(B_60))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_158])).
% 2.33/1.35  tff(c_111, plain, (![A_49, A_17]: (k2_xboole_0(k1_tarski(A_49), k1_tarski(A_17))=k1_enumset1(A_49, A_17, A_17))), inference(superposition, [status(thm), theory('equality')], [c_32, c_102])).
% 2.33/1.35  tff(c_199, plain, (![B_60]: (k1_enumset1(B_60, B_60, B_60)=k1_tarski(B_60))), inference(superposition, [status(thm), theory('equality')], [c_190, c_111])).
% 2.33/1.35  tff(c_263, plain, (![E_64, C_65, B_66, A_67]: (E_64=C_65 | E_64=B_66 | E_64=A_67 | ~r2_hidden(E_64, k1_enumset1(A_67, B_66, C_65)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.33/1.35  tff(c_484, plain, (![E_84, B_85]: (E_84=B_85 | E_84=B_85 | E_84=B_85 | ~r2_hidden(E_84, k1_tarski(B_85)))), inference(superposition, [status(thm), theory('equality')], [c_199, c_263])).
% 2.33/1.35  tff(c_487, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_174, c_484])).
% 2.33/1.35  tff(c_494, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_40, c_40, c_487])).
% 2.33/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.35  
% 2.33/1.35  Inference rules
% 2.33/1.35  ----------------------
% 2.33/1.35  #Ref     : 0
% 2.33/1.35  #Sup     : 107
% 2.33/1.35  #Fact    : 0
% 2.33/1.35  #Define  : 0
% 2.33/1.35  #Split   : 0
% 2.33/1.35  #Chain   : 0
% 2.33/1.35  #Close   : 0
% 2.33/1.35  
% 2.33/1.35  Ordering : KBO
% 2.33/1.35  
% 2.33/1.35  Simplification rules
% 2.33/1.35  ----------------------
% 2.33/1.35  #Subsume      : 2
% 2.33/1.35  #Demod        : 59
% 2.33/1.35  #Tautology    : 82
% 2.33/1.35  #SimpNegUnit  : 3
% 2.33/1.35  #BackRed      : 0
% 2.33/1.35  
% 2.33/1.35  #Partial instantiations: 0
% 2.33/1.35  #Strategies tried      : 1
% 2.33/1.35  
% 2.33/1.35  Timing (in seconds)
% 2.33/1.35  ----------------------
% 2.42/1.36  Preprocessing        : 0.29
% 2.42/1.36  Parsing              : 0.15
% 2.42/1.36  CNF conversion       : 0.02
% 2.42/1.36  Main loop            : 0.23
% 2.42/1.36  Inferencing          : 0.09
% 2.42/1.36  Reduction            : 0.08
% 2.42/1.36  Demodulation         : 0.06
% 2.42/1.36  BG Simplification    : 0.01
% 2.42/1.36  Subsumption          : 0.03
% 2.42/1.36  Abstraction          : 0.01
% 2.42/1.36  MUC search           : 0.00
% 2.42/1.36  Cooper               : 0.00
% 2.42/1.36  Total                : 0.55
% 2.42/1.36  Index Insertion      : 0.00
% 2.42/1.36  Index Deletion       : 0.00
% 2.42/1.36  Index Matching       : 0.00
% 2.42/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
