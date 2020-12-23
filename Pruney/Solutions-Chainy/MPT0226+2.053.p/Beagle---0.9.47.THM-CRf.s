%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:44 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   42 (  49 expanded)
%              Number of leaves         :   24 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   39 (  53 expanded)
%              Number of equality atoms :   31 (  44 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_29,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_50,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_40,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_32,plain,(
    ! [A_13,B_14] : k2_xboole_0(k1_tarski(A_13),k1_tarski(B_14)) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_42,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_106,plain,(
    ! [A_41,B_42] : k5_xboole_0(A_41,k4_xboole_0(B_42,A_41)) = k2_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_115,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k5_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_106])).

tff(c_118,plain,(
    k2_tarski('#skF_4','#skF_3') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_4,c_115])).

tff(c_68,plain,(
    ! [A_32,B_33] : k1_enumset1(A_32,A_32,B_33) = k2_tarski(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_10,plain,(
    ! [E_12,A_6,B_7] : r2_hidden(E_12,k1_enumset1(A_6,B_7,E_12)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_77,plain,(
    ! [B_33,A_32] : r2_hidden(B_33,k2_tarski(A_32,B_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_10])).

tff(c_122,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_77])).

tff(c_34,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_36,plain,(
    ! [A_16,B_17] : k1_enumset1(A_16,A_16,B_17) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_148,plain,(
    ! [E_48,C_49,B_50,A_51] :
      ( E_48 = C_49
      | E_48 = B_50
      | E_48 = A_51
      | ~ r2_hidden(E_48,k1_enumset1(A_51,B_50,C_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_168,plain,(
    ! [E_56,B_57,A_58] :
      ( E_56 = B_57
      | E_56 = A_58
      | E_56 = A_58
      | ~ r2_hidden(E_56,k2_tarski(A_58,B_57)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_148])).

tff(c_201,plain,(
    ! [E_60,A_61] :
      ( E_60 = A_61
      | E_60 = A_61
      | E_60 = A_61
      | ~ r2_hidden(E_60,k1_tarski(A_61)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_168])).

tff(c_204,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_122,c_201])).

tff(c_211,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_40,c_40,c_204])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:42:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.25  
% 2.05/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.25  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.05/1.25  
% 2.05/1.25  %Foreground sorts:
% 2.05/1.25  
% 2.05/1.25  
% 2.05/1.25  %Background operators:
% 2.05/1.25  
% 2.05/1.25  
% 2.05/1.25  %Foreground operators:
% 2.05/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.05/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.05/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.05/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.05/1.25  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.05/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.05/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.05/1.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.05/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.05/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.05/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.05/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.05/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.05/1.25  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.05/1.25  
% 2.05/1.26  tff(f_59, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 2.05/1.26  tff(f_48, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.05/1.26  tff(f_29, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.05/1.26  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.05/1.26  tff(f_52, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.05/1.26  tff(f_46, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.05/1.26  tff(f_50, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.05/1.26  tff(c_40, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.05/1.26  tff(c_32, plain, (![A_13, B_14]: (k2_xboole_0(k1_tarski(A_13), k1_tarski(B_14))=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.05/1.26  tff(c_4, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.05/1.26  tff(c_42, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.05/1.26  tff(c_106, plain, (![A_41, B_42]: (k5_xboole_0(A_41, k4_xboole_0(B_42, A_41))=k2_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.05/1.26  tff(c_115, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k5_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_42, c_106])).
% 2.05/1.26  tff(c_118, plain, (k2_tarski('#skF_4', '#skF_3')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_4, c_115])).
% 2.05/1.26  tff(c_68, plain, (![A_32, B_33]: (k1_enumset1(A_32, A_32, B_33)=k2_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.05/1.26  tff(c_10, plain, (![E_12, A_6, B_7]: (r2_hidden(E_12, k1_enumset1(A_6, B_7, E_12)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.05/1.26  tff(c_77, plain, (![B_33, A_32]: (r2_hidden(B_33, k2_tarski(A_32, B_33)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_10])).
% 2.05/1.26  tff(c_122, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_118, c_77])).
% 2.05/1.26  tff(c_34, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.05/1.26  tff(c_36, plain, (![A_16, B_17]: (k1_enumset1(A_16, A_16, B_17)=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.05/1.26  tff(c_148, plain, (![E_48, C_49, B_50, A_51]: (E_48=C_49 | E_48=B_50 | E_48=A_51 | ~r2_hidden(E_48, k1_enumset1(A_51, B_50, C_49)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.05/1.26  tff(c_168, plain, (![E_56, B_57, A_58]: (E_56=B_57 | E_56=A_58 | E_56=A_58 | ~r2_hidden(E_56, k2_tarski(A_58, B_57)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_148])).
% 2.05/1.26  tff(c_201, plain, (![E_60, A_61]: (E_60=A_61 | E_60=A_61 | E_60=A_61 | ~r2_hidden(E_60, k1_tarski(A_61)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_168])).
% 2.05/1.26  tff(c_204, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_122, c_201])).
% 2.05/1.26  tff(c_211, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_40, c_40, c_204])).
% 2.05/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.26  
% 2.05/1.26  Inference rules
% 2.05/1.26  ----------------------
% 2.05/1.26  #Ref     : 0
% 2.05/1.26  #Sup     : 38
% 2.05/1.26  #Fact    : 0
% 2.05/1.26  #Define  : 0
% 2.05/1.26  #Split   : 0
% 2.05/1.26  #Chain   : 0
% 2.05/1.26  #Close   : 0
% 2.05/1.26  
% 2.05/1.26  Ordering : KBO
% 2.05/1.26  
% 2.05/1.26  Simplification rules
% 2.05/1.26  ----------------------
% 2.05/1.26  #Subsume      : 0
% 2.05/1.26  #Demod        : 5
% 2.05/1.26  #Tautology    : 28
% 2.05/1.26  #SimpNegUnit  : 3
% 2.05/1.26  #BackRed      : 0
% 2.05/1.26  
% 2.05/1.26  #Partial instantiations: 0
% 2.05/1.26  #Strategies tried      : 1
% 2.05/1.26  
% 2.05/1.26  Timing (in seconds)
% 2.05/1.26  ----------------------
% 2.05/1.27  Preprocessing        : 0.30
% 2.05/1.27  Parsing              : 0.15
% 2.05/1.27  CNF conversion       : 0.02
% 2.05/1.27  Main loop            : 0.19
% 2.05/1.27  Inferencing          : 0.08
% 2.05/1.27  Reduction            : 0.05
% 2.05/1.27  Demodulation         : 0.04
% 2.05/1.27  BG Simplification    : 0.01
% 2.05/1.27  Subsumption          : 0.03
% 2.05/1.27  Abstraction          : 0.01
% 2.05/1.27  MUC search           : 0.00
% 2.05/1.27  Cooper               : 0.00
% 2.05/1.27  Total                : 0.52
% 2.05/1.27  Index Insertion      : 0.00
% 2.05/1.27  Index Deletion       : 0.00
% 2.05/1.27  Index Matching       : 0.00
% 2.05/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
