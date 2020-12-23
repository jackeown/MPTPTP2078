%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:38 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   47 (  49 expanded)
%              Number of leaves         :   28 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   35 (  38 expanded)
%              Number of equality atoms :   28 (  31 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_63,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_29,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_60,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_54,plain,(
    ! [A_28,B_29] : k1_enumset1(A_28,A_28,B_29) = k2_tarski(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_52,plain,(
    ! [A_27] : k2_tarski(A_27,A_27) = k1_tarski(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_225,plain,(
    ! [A_67,B_68,C_69] : k2_xboole_0(k2_tarski(A_67,B_68),k1_tarski(C_69)) = k1_enumset1(A_67,B_68,C_69) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_240,plain,(
    ! [A_27,C_69] : k2_xboole_0(k1_tarski(A_27),k1_tarski(C_69)) = k1_enumset1(A_27,A_27,C_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_225])).

tff(c_244,plain,(
    ! [A_70,C_71] : k2_xboole_0(k1_tarski(A_70),k1_tarski(C_71)) = k2_tarski(A_70,C_71) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_240])).

tff(c_4,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_62,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_199,plain,(
    ! [A_62,B_63] : k5_xboole_0(A_62,k4_xboole_0(B_63,A_62)) = k2_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_208,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_5')) = k5_xboole_0(k1_tarski('#skF_6'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_199])).

tff(c_211,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_5')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_208])).

tff(c_250,plain,(
    k2_tarski('#skF_6','#skF_5') = k1_tarski('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_211])).

tff(c_145,plain,(
    ! [A_54,B_55] : k1_enumset1(A_54,A_54,B_55) = k2_tarski(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_16,plain,(
    ! [E_18,A_12,B_13] : r2_hidden(E_18,k1_enumset1(A_12,B_13,E_18)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_157,plain,(
    ! [B_55,A_54] : r2_hidden(B_55,k2_tarski(A_54,B_55)) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_16])).

tff(c_265,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_157])).

tff(c_38,plain,(
    ! [C_23,A_19] :
      ( C_23 = A_19
      | ~ r2_hidden(C_23,k1_tarski(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_276,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_265,c_38])).

tff(c_280,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_276])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:29:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.28  
% 1.99/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.28  %$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4
% 1.99/1.28  
% 1.99/1.28  %Foreground sorts:
% 1.99/1.28  
% 1.99/1.28  
% 1.99/1.28  %Background operators:
% 1.99/1.28  
% 1.99/1.28  
% 1.99/1.28  %Foreground operators:
% 1.99/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.99/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.99/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.99/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.99/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.99/1.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.99/1.28  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.99/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.99/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.99/1.28  tff('#skF_5', type, '#skF_5': $i).
% 1.99/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 1.99/1.28  tff('#skF_6', type, '#skF_6': $i).
% 1.99/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.99/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.99/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.99/1.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 1.99/1.28  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.99/1.28  
% 1.99/1.29  tff(f_74, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 1.99/1.29  tff(f_65, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.99/1.29  tff(f_63, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.99/1.29  tff(f_61, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 1.99/1.29  tff(f_29, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 1.99/1.29  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 1.99/1.29  tff(f_52, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 1.99/1.29  tff(f_59, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.99/1.29  tff(c_60, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.99/1.29  tff(c_54, plain, (![A_28, B_29]: (k1_enumset1(A_28, A_28, B_29)=k2_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.99/1.29  tff(c_52, plain, (![A_27]: (k2_tarski(A_27, A_27)=k1_tarski(A_27))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.99/1.29  tff(c_225, plain, (![A_67, B_68, C_69]: (k2_xboole_0(k2_tarski(A_67, B_68), k1_tarski(C_69))=k1_enumset1(A_67, B_68, C_69))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.99/1.29  tff(c_240, plain, (![A_27, C_69]: (k2_xboole_0(k1_tarski(A_27), k1_tarski(C_69))=k1_enumset1(A_27, A_27, C_69))), inference(superposition, [status(thm), theory('equality')], [c_52, c_225])).
% 1.99/1.29  tff(c_244, plain, (![A_70, C_71]: (k2_xboole_0(k1_tarski(A_70), k1_tarski(C_71))=k2_tarski(A_70, C_71))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_240])).
% 1.99/1.29  tff(c_4, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.99/1.29  tff(c_62, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.99/1.29  tff(c_199, plain, (![A_62, B_63]: (k5_xboole_0(A_62, k4_xboole_0(B_63, A_62))=k2_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.99/1.29  tff(c_208, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_5'))=k5_xboole_0(k1_tarski('#skF_6'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_62, c_199])).
% 1.99/1.29  tff(c_211, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_5'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_208])).
% 1.99/1.29  tff(c_250, plain, (k2_tarski('#skF_6', '#skF_5')=k1_tarski('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_244, c_211])).
% 1.99/1.29  tff(c_145, plain, (![A_54, B_55]: (k1_enumset1(A_54, A_54, B_55)=k2_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.99/1.29  tff(c_16, plain, (![E_18, A_12, B_13]: (r2_hidden(E_18, k1_enumset1(A_12, B_13, E_18)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.99/1.29  tff(c_157, plain, (![B_55, A_54]: (r2_hidden(B_55, k2_tarski(A_54, B_55)))), inference(superposition, [status(thm), theory('equality')], [c_145, c_16])).
% 1.99/1.29  tff(c_265, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_250, c_157])).
% 1.99/1.29  tff(c_38, plain, (![C_23, A_19]: (C_23=A_19 | ~r2_hidden(C_23, k1_tarski(A_19)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.99/1.29  tff(c_276, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_265, c_38])).
% 1.99/1.29  tff(c_280, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_276])).
% 1.99/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.29  
% 1.99/1.29  Inference rules
% 1.99/1.29  ----------------------
% 1.99/1.29  #Ref     : 0
% 1.99/1.29  #Sup     : 54
% 1.99/1.29  #Fact    : 0
% 1.99/1.29  #Define  : 0
% 1.99/1.29  #Split   : 0
% 1.99/1.29  #Chain   : 0
% 1.99/1.29  #Close   : 0
% 1.99/1.29  
% 1.99/1.29  Ordering : KBO
% 1.99/1.29  
% 1.99/1.29  Simplification rules
% 1.99/1.29  ----------------------
% 1.99/1.29  #Subsume      : 0
% 1.99/1.29  #Demod        : 11
% 1.99/1.29  #Tautology    : 43
% 1.99/1.29  #SimpNegUnit  : 1
% 1.99/1.29  #BackRed      : 0
% 1.99/1.29  
% 1.99/1.29  #Partial instantiations: 0
% 1.99/1.29  #Strategies tried      : 1
% 1.99/1.29  
% 1.99/1.29  Timing (in seconds)
% 1.99/1.29  ----------------------
% 1.99/1.29  Preprocessing        : 0.33
% 1.99/1.29  Parsing              : 0.17
% 1.99/1.29  CNF conversion       : 0.02
% 1.99/1.29  Main loop            : 0.17
% 1.99/1.29  Inferencing          : 0.05
% 1.99/1.29  Reduction            : 0.06
% 1.99/1.30  Demodulation         : 0.05
% 1.99/1.30  BG Simplification    : 0.01
% 1.99/1.30  Subsumption          : 0.03
% 1.99/1.30  Abstraction          : 0.01
% 1.99/1.30  MUC search           : 0.00
% 1.99/1.30  Cooper               : 0.00
% 1.99/1.30  Total                : 0.52
% 1.99/1.30  Index Insertion      : 0.00
% 1.99/1.30  Index Deletion       : 0.00
% 1.99/1.30  Index Matching       : 0.00
% 1.99/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
