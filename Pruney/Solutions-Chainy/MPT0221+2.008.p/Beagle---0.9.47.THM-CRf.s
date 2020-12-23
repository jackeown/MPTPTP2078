%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:13 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   42 (  43 expanded)
%              Number of leaves         :   25 (  26 expanded)
%              Depth                    :    5
%              Number of atoms          :   39 (  41 expanded)
%              Number of equality atoms :   16 (  17 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(f_43,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
          & A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_72,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_74,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_8,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_123,plain,(
    ! [A_46,B_47,C_48] :
      ( ~ r1_xboole_0(A_46,B_47)
      | ~ r2_hidden(C_48,k3_xboole_0(A_46,B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_126,plain,(
    ! [A_6,C_48] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_48,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_123])).

tff(c_128,plain,(
    ! [C_48] : ~ r2_hidden(C_48,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_126])).

tff(c_46,plain,(
    '#skF_5' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_48,plain,(
    r1_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_49,plain,(
    r1_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48])).

tff(c_72,plain,(
    ! [A_29] :
      ( ~ r1_xboole_0(A_29,A_29)
      | k1_xboole_0 = A_29 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_80,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_49,c_72])).

tff(c_38,plain,(
    ! [A_16] : k2_tarski(A_16,A_16) = k1_tarski(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_92,plain,(
    ! [A_39,B_40] : k1_enumset1(A_39,A_39,B_40) = k2_tarski(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_18,plain,(
    ! [E_15,A_9,C_11] : r2_hidden(E_15,k1_enumset1(A_9,E_15,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_110,plain,(
    ! [A_41,B_42] : r2_hidden(A_41,k2_tarski(A_41,B_42)) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_18])).

tff(c_114,plain,(
    ! [A_43] : r2_hidden(A_43,k1_tarski(A_43)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_110])).

tff(c_117,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_114])).

tff(c_130,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_117])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:16:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.18  
% 1.81/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.18  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 1.81/1.18  
% 1.81/1.18  %Foreground sorts:
% 1.81/1.18  
% 1.81/1.18  
% 1.81/1.18  %Background operators:
% 1.81/1.18  
% 1.81/1.18  
% 1.81/1.18  %Foreground operators:
% 1.81/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.81/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.81/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.81/1.18  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.81/1.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.81/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.81/1.18  tff('#skF_5', type, '#skF_5': $i).
% 1.81/1.18  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 1.81/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.81/1.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.81/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.81/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.81/1.18  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 1.81/1.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.81/1.18  
% 1.81/1.19  tff(f_43, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.81/1.19  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.81/1.19  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.81/1.19  tff(f_84, negated_conjecture, ~(![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 1.81/1.19  tff(f_55, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 1.81/1.19  tff(f_72, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.81/1.19  tff(f_74, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.81/1.19  tff(f_70, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 1.81/1.19  tff(c_8, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.81/1.19  tff(c_6, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.81/1.19  tff(c_123, plain, (![A_46, B_47, C_48]: (~r1_xboole_0(A_46, B_47) | ~r2_hidden(C_48, k3_xboole_0(A_46, B_47)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.81/1.19  tff(c_126, plain, (![A_6, C_48]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_48, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_123])).
% 1.81/1.19  tff(c_128, plain, (![C_48]: (~r2_hidden(C_48, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_126])).
% 1.81/1.19  tff(c_46, plain, ('#skF_5'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_84])).
% 1.81/1.19  tff(c_48, plain, (r1_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 1.81/1.19  tff(c_49, plain, (r1_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48])).
% 1.81/1.19  tff(c_72, plain, (![A_29]: (~r1_xboole_0(A_29, A_29) | k1_xboole_0=A_29)), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.81/1.19  tff(c_80, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_49, c_72])).
% 1.81/1.19  tff(c_38, plain, (![A_16]: (k2_tarski(A_16, A_16)=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.81/1.19  tff(c_92, plain, (![A_39, B_40]: (k1_enumset1(A_39, A_39, B_40)=k2_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.81/1.19  tff(c_18, plain, (![E_15, A_9, C_11]: (r2_hidden(E_15, k1_enumset1(A_9, E_15, C_11)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.81/1.19  tff(c_110, plain, (![A_41, B_42]: (r2_hidden(A_41, k2_tarski(A_41, B_42)))), inference(superposition, [status(thm), theory('equality')], [c_92, c_18])).
% 1.81/1.19  tff(c_114, plain, (![A_43]: (r2_hidden(A_43, k1_tarski(A_43)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_110])).
% 1.81/1.19  tff(c_117, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_80, c_114])).
% 1.81/1.19  tff(c_130, plain, $false, inference(negUnitSimplification, [status(thm)], [c_128, c_117])).
% 1.81/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.19  
% 1.81/1.19  Inference rules
% 1.81/1.19  ----------------------
% 1.81/1.19  #Ref     : 0
% 1.81/1.19  #Sup     : 19
% 1.81/1.19  #Fact    : 0
% 1.81/1.19  #Define  : 0
% 1.81/1.19  #Split   : 0
% 1.81/1.19  #Chain   : 0
% 1.81/1.19  #Close   : 0
% 1.81/1.19  
% 1.81/1.19  Ordering : KBO
% 1.81/1.19  
% 1.81/1.19  Simplification rules
% 1.81/1.19  ----------------------
% 1.81/1.19  #Subsume      : 0
% 1.81/1.19  #Demod        : 7
% 1.81/1.19  #Tautology    : 14
% 1.81/1.19  #SimpNegUnit  : 1
% 1.81/1.19  #BackRed      : 2
% 1.81/1.19  
% 1.81/1.19  #Partial instantiations: 0
% 1.81/1.19  #Strategies tried      : 1
% 1.81/1.19  
% 1.81/1.19  Timing (in seconds)
% 1.81/1.19  ----------------------
% 1.81/1.20  Preprocessing        : 0.30
% 1.81/1.20  Parsing              : 0.16
% 1.81/1.20  CNF conversion       : 0.02
% 1.81/1.20  Main loop            : 0.11
% 1.81/1.20  Inferencing          : 0.03
% 1.81/1.20  Reduction            : 0.04
% 1.81/1.20  Demodulation         : 0.03
% 1.81/1.20  BG Simplification    : 0.01
% 1.81/1.20  Subsumption          : 0.02
% 1.81/1.20  Abstraction          : 0.01
% 1.81/1.20  MUC search           : 0.00
% 1.81/1.20  Cooper               : 0.00
% 1.81/1.20  Total                : 0.44
% 1.81/1.20  Index Insertion      : 0.00
% 1.81/1.20  Index Deletion       : 0.00
% 1.81/1.20  Index Matching       : 0.00
% 1.81/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
