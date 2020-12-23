%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:02 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   37 (  54 expanded)
%              Number of leaves         :   20 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   33 (  57 expanded)
%              Number of equality atoms :   27 (  50 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_57,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_48,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_44,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_42,axiom,(
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

tff(c_38,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_32,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_104,plain,(
    ! [A_45,B_46,C_47] : k2_xboole_0(k1_tarski(A_45),k2_tarski(B_46,C_47)) = k1_enumset1(A_45,B_46,C_47) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_116,plain,(
    ! [A_48,A_49] : k2_xboole_0(k1_tarski(A_48),k1_tarski(A_49)) = k1_enumset1(A_48,A_49,A_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_104])).

tff(c_40,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_125,plain,(
    k1_enumset1('#skF_3','#skF_4','#skF_4') = k1_tarski('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_40])).

tff(c_6,plain,(
    ! [E_9,A_3,B_4] : r2_hidden(E_9,k1_enumset1(A_3,B_4,E_9)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_186,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_6])).

tff(c_34,plain,(
    ! [A_18,B_19] : k1_enumset1(A_18,A_18,B_19) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_151,plain,(
    ! [B_19] : k2_xboole_0(k1_tarski(B_19),k1_tarski(B_19)) = k2_tarski(B_19,B_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_116])).

tff(c_199,plain,(
    ! [B_54] : k2_xboole_0(k1_tarski(B_54),k1_tarski(B_54)) = k1_tarski(B_54) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_151])).

tff(c_113,plain,(
    ! [A_45,A_17] : k2_xboole_0(k1_tarski(A_45),k1_tarski(A_17)) = k1_enumset1(A_45,A_17,A_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_104])).

tff(c_215,plain,(
    ! [B_55] : k1_enumset1(B_55,B_55,B_55) = k1_tarski(B_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_113])).

tff(c_4,plain,(
    ! [E_9,C_5,B_4,A_3] :
      ( E_9 = C_5
      | E_9 = B_4
      | E_9 = A_3
      | ~ r2_hidden(E_9,k1_enumset1(A_3,B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_477,plain,(
    ! [E_76,B_77] :
      ( E_76 = B_77
      | E_76 = B_77
      | E_76 = B_77
      | ~ r2_hidden(E_76,k1_tarski(B_77)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_4])).

tff(c_480,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_186,c_477])).

tff(c_487,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_38,c_38,c_480])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:57:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.25  
% 2.08/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.26  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.08/1.26  
% 2.08/1.26  %Foreground sorts:
% 2.08/1.26  
% 2.08/1.26  
% 2.08/1.26  %Background operators:
% 2.08/1.26  
% 2.08/1.26  
% 2.08/1.26  %Foreground operators:
% 2.08/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.08/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.08/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.08/1.26  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.08/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.08/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.08/1.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.08/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.08/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.08/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.08/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.08/1.26  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.08/1.26  
% 2.22/1.27  tff(f_57, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 2.22/1.27  tff(f_48, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.22/1.27  tff(f_44, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 2.22/1.27  tff(f_42, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.22/1.27  tff(f_50, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.22/1.27  tff(c_38, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.22/1.27  tff(c_32, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.22/1.27  tff(c_104, plain, (![A_45, B_46, C_47]: (k2_xboole_0(k1_tarski(A_45), k2_tarski(B_46, C_47))=k1_enumset1(A_45, B_46, C_47))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.22/1.27  tff(c_116, plain, (![A_48, A_49]: (k2_xboole_0(k1_tarski(A_48), k1_tarski(A_49))=k1_enumset1(A_48, A_49, A_49))), inference(superposition, [status(thm), theory('equality')], [c_32, c_104])).
% 2.22/1.27  tff(c_40, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.22/1.27  tff(c_125, plain, (k1_enumset1('#skF_3', '#skF_4', '#skF_4')=k1_tarski('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_116, c_40])).
% 2.22/1.27  tff(c_6, plain, (![E_9, A_3, B_4]: (r2_hidden(E_9, k1_enumset1(A_3, B_4, E_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.22/1.27  tff(c_186, plain, (r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_125, c_6])).
% 2.22/1.27  tff(c_34, plain, (![A_18, B_19]: (k1_enumset1(A_18, A_18, B_19)=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.22/1.27  tff(c_151, plain, (![B_19]: (k2_xboole_0(k1_tarski(B_19), k1_tarski(B_19))=k2_tarski(B_19, B_19))), inference(superposition, [status(thm), theory('equality')], [c_34, c_116])).
% 2.22/1.27  tff(c_199, plain, (![B_54]: (k2_xboole_0(k1_tarski(B_54), k1_tarski(B_54))=k1_tarski(B_54))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_151])).
% 2.22/1.27  tff(c_113, plain, (![A_45, A_17]: (k2_xboole_0(k1_tarski(A_45), k1_tarski(A_17))=k1_enumset1(A_45, A_17, A_17))), inference(superposition, [status(thm), theory('equality')], [c_32, c_104])).
% 2.22/1.27  tff(c_215, plain, (![B_55]: (k1_enumset1(B_55, B_55, B_55)=k1_tarski(B_55))), inference(superposition, [status(thm), theory('equality')], [c_199, c_113])).
% 2.22/1.27  tff(c_4, plain, (![E_9, C_5, B_4, A_3]: (E_9=C_5 | E_9=B_4 | E_9=A_3 | ~r2_hidden(E_9, k1_enumset1(A_3, B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.22/1.27  tff(c_477, plain, (![E_76, B_77]: (E_76=B_77 | E_76=B_77 | E_76=B_77 | ~r2_hidden(E_76, k1_tarski(B_77)))), inference(superposition, [status(thm), theory('equality')], [c_215, c_4])).
% 2.22/1.27  tff(c_480, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_186, c_477])).
% 2.22/1.27  tff(c_487, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_38, c_38, c_480])).
% 2.22/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.27  
% 2.22/1.27  Inference rules
% 2.22/1.27  ----------------------
% 2.22/1.27  #Ref     : 0
% 2.22/1.27  #Sup     : 106
% 2.22/1.27  #Fact    : 0
% 2.22/1.27  #Define  : 0
% 2.22/1.27  #Split   : 0
% 2.22/1.27  #Chain   : 0
% 2.22/1.27  #Close   : 0
% 2.22/1.27  
% 2.22/1.27  Ordering : KBO
% 2.22/1.27  
% 2.22/1.27  Simplification rules
% 2.22/1.27  ----------------------
% 2.22/1.27  #Subsume      : 2
% 2.22/1.27  #Demod        : 61
% 2.22/1.27  #Tautology    : 82
% 2.22/1.27  #SimpNegUnit  : 3
% 2.22/1.27  #BackRed      : 0
% 2.22/1.27  
% 2.22/1.27  #Partial instantiations: 0
% 2.22/1.27  #Strategies tried      : 1
% 2.22/1.27  
% 2.22/1.27  Timing (in seconds)
% 2.22/1.27  ----------------------
% 2.22/1.27  Preprocessing        : 0.29
% 2.22/1.27  Parsing              : 0.15
% 2.22/1.27  CNF conversion       : 0.02
% 2.22/1.27  Main loop            : 0.22
% 2.22/1.27  Inferencing          : 0.08
% 2.22/1.27  Reduction            : 0.08
% 2.22/1.27  Demodulation         : 0.06
% 2.22/1.27  BG Simplification    : 0.01
% 2.22/1.27  Subsumption          : 0.03
% 2.22/1.27  Abstraction          : 0.01
% 2.22/1.27  MUC search           : 0.00
% 2.22/1.27  Cooper               : 0.00
% 2.22/1.27  Total                : 0.53
% 2.22/1.27  Index Insertion      : 0.00
% 2.22/1.27  Index Deletion       : 0.00
% 2.22/1.27  Index Matching       : 0.00
% 2.22/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
