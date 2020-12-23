%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:20 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   44 (  61 expanded)
%              Number of leaves         :   22 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :   51 (  82 expanded)
%              Number of equality atoms :   25 (  45 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_58,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_60,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_32,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_89,plain,(
    ! [A_37,B_38] : k1_enumset1(A_37,A_37,B_38) = k2_tarski(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_14,plain,(
    ! [E_14,B_9,C_10] : r2_hidden(E_14,k1_enumset1(E_14,B_9,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_107,plain,(
    ! [A_39,B_40] : r2_hidden(A_39,k2_tarski(A_39,B_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_14])).

tff(c_110,plain,(
    ! [A_15] : r2_hidden(A_15,k1_tarski(A_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_107])).

tff(c_40,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_38,plain,(
    ! [A_21,B_22] :
      ( r1_xboole_0(k1_tarski(A_21),B_22)
      | r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_42,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_122,plain,(
    ! [A_44,B_45,C_46] :
      ( ~ r1_xboole_0(A_44,B_45)
      | ~ r2_hidden(C_46,k3_xboole_0(A_44,B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_132,plain,(
    ! [A_47,B_48,C_49] :
      ( ~ r1_xboole_0(A_47,B_48)
      | ~ r2_hidden(C_49,k3_xboole_0(B_48,A_47)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_122])).

tff(c_135,plain,(
    ! [C_49] :
      ( ~ r1_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_4'))
      | ~ r2_hidden(C_49,k1_tarski('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_132])).

tff(c_156,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_160,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_38,c_156])).

tff(c_34,plain,(
    ! [A_16,B_17] : k1_enumset1(A_16,A_16,B_17) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_184,plain,(
    ! [E_57,C_58,B_59,A_60] :
      ( E_57 = C_58
      | E_57 = B_59
      | E_57 = A_60
      | ~ r2_hidden(E_57,k1_enumset1(A_60,B_59,C_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_236,plain,(
    ! [E_65,B_66,A_67] :
      ( E_65 = B_66
      | E_65 = A_67
      | E_65 = A_67
      | ~ r2_hidden(E_65,k2_tarski(A_67,B_66)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_184])).

tff(c_250,plain,(
    ! [E_68,A_69] :
      ( E_68 = A_69
      | E_68 = A_69
      | E_68 = A_69
      | ~ r2_hidden(E_68,k1_tarski(A_69)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_236])).

tff(c_259,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_160,c_250])).

tff(c_271,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_40,c_40,c_259])).

tff(c_274,plain,(
    ! [C_70] : ~ r2_hidden(C_70,k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_279,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_110,c_274])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:50:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.29  
% 1.96/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.29  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 1.96/1.29  
% 1.96/1.29  %Foreground sorts:
% 1.96/1.29  
% 1.96/1.29  
% 1.96/1.29  %Background operators:
% 1.96/1.29  
% 1.96/1.29  
% 1.96/1.29  %Foreground operators:
% 1.96/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.96/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.96/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.96/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.96/1.29  tff('#skF_5', type, '#skF_5': $i).
% 1.96/1.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 1.96/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.96/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.96/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.29  tff('#skF_4', type, '#skF_4': $i).
% 1.96/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.96/1.29  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 1.96/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.96/1.29  
% 1.96/1.30  tff(f_58, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.96/1.30  tff(f_60, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.96/1.30  tff(f_56, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 1.96/1.30  tff(f_72, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 1.96/1.30  tff(f_67, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 1.96/1.30  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.96/1.30  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.96/1.30  tff(c_32, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.96/1.30  tff(c_89, plain, (![A_37, B_38]: (k1_enumset1(A_37, A_37, B_38)=k2_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.96/1.30  tff(c_14, plain, (![E_14, B_9, C_10]: (r2_hidden(E_14, k1_enumset1(E_14, B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.96/1.30  tff(c_107, plain, (![A_39, B_40]: (r2_hidden(A_39, k2_tarski(A_39, B_40)))), inference(superposition, [status(thm), theory('equality')], [c_89, c_14])).
% 1.96/1.30  tff(c_110, plain, (![A_15]: (r2_hidden(A_15, k1_tarski(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_107])).
% 1.96/1.30  tff(c_40, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.96/1.30  tff(c_38, plain, (![A_21, B_22]: (r1_xboole_0(k1_tarski(A_21), B_22) | r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.96/1.30  tff(c_42, plain, (k3_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.96/1.30  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.96/1.30  tff(c_122, plain, (![A_44, B_45, C_46]: (~r1_xboole_0(A_44, B_45) | ~r2_hidden(C_46, k3_xboole_0(A_44, B_45)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.96/1.30  tff(c_132, plain, (![A_47, B_48, C_49]: (~r1_xboole_0(A_47, B_48) | ~r2_hidden(C_49, k3_xboole_0(B_48, A_47)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_122])).
% 1.96/1.30  tff(c_135, plain, (![C_49]: (~r1_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_4')) | ~r2_hidden(C_49, k1_tarski('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_42, c_132])).
% 1.96/1.30  tff(c_156, plain, (~r1_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_135])).
% 1.96/1.30  tff(c_160, plain, (r2_hidden('#skF_5', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_38, c_156])).
% 1.96/1.30  tff(c_34, plain, (![A_16, B_17]: (k1_enumset1(A_16, A_16, B_17)=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.96/1.30  tff(c_184, plain, (![E_57, C_58, B_59, A_60]: (E_57=C_58 | E_57=B_59 | E_57=A_60 | ~r2_hidden(E_57, k1_enumset1(A_60, B_59, C_58)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.96/1.30  tff(c_236, plain, (![E_65, B_66, A_67]: (E_65=B_66 | E_65=A_67 | E_65=A_67 | ~r2_hidden(E_65, k2_tarski(A_67, B_66)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_184])).
% 1.96/1.30  tff(c_250, plain, (![E_68, A_69]: (E_68=A_69 | E_68=A_69 | E_68=A_69 | ~r2_hidden(E_68, k1_tarski(A_69)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_236])).
% 1.96/1.30  tff(c_259, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_160, c_250])).
% 1.96/1.30  tff(c_271, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_40, c_40, c_259])).
% 1.96/1.30  tff(c_274, plain, (![C_70]: (~r2_hidden(C_70, k1_tarski('#skF_4')))), inference(splitRight, [status(thm)], [c_135])).
% 1.96/1.30  tff(c_279, plain, $false, inference(resolution, [status(thm)], [c_110, c_274])).
% 1.96/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.30  
% 1.96/1.30  Inference rules
% 1.96/1.30  ----------------------
% 1.96/1.30  #Ref     : 0
% 1.96/1.30  #Sup     : 56
% 1.96/1.30  #Fact    : 0
% 1.96/1.30  #Define  : 0
% 1.96/1.30  #Split   : 2
% 1.96/1.30  #Chain   : 0
% 1.96/1.30  #Close   : 0
% 1.96/1.30  
% 1.96/1.30  Ordering : KBO
% 1.96/1.30  
% 1.96/1.30  Simplification rules
% 1.96/1.30  ----------------------
% 1.96/1.30  #Subsume      : 8
% 1.96/1.30  #Demod        : 4
% 1.96/1.30  #Tautology    : 27
% 1.96/1.30  #SimpNegUnit  : 3
% 1.96/1.30  #BackRed      : 0
% 1.96/1.30  
% 1.96/1.30  #Partial instantiations: 0
% 1.96/1.30  #Strategies tried      : 1
% 1.96/1.30  
% 1.96/1.30  Timing (in seconds)
% 1.96/1.30  ----------------------
% 1.96/1.31  Preprocessing        : 0.29
% 1.96/1.31  Parsing              : 0.15
% 1.96/1.31  CNF conversion       : 0.02
% 1.96/1.31  Main loop            : 0.19
% 1.96/1.31  Inferencing          : 0.07
% 1.96/1.31  Reduction            : 0.06
% 1.96/1.31  Demodulation         : 0.05
% 1.96/1.31  BG Simplification    : 0.01
% 1.96/1.31  Subsumption          : 0.04
% 1.96/1.31  Abstraction          : 0.01
% 1.96/1.31  MUC search           : 0.00
% 1.96/1.31  Cooper               : 0.00
% 1.96/1.31  Total                : 0.50
% 1.96/1.31  Index Insertion      : 0.00
% 1.96/1.31  Index Deletion       : 0.00
% 1.96/1.31  Index Matching       : 0.00
% 1.96/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
