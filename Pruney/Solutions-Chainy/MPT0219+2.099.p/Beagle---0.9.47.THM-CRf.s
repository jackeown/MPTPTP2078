%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:02 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   45 (  75 expanded)
%              Number of leaves         :   23 (  37 expanded)
%              Depth                    :   12
%              Number of atoms          :   40 (  77 expanded)
%              Number of equality atoms :   34 (  70 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_52,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_48,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_44,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_38,plain,(
    ! [A_26,B_27] : k1_enumset1(A_26,A_26,B_27) = k2_tarski(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_36,plain,(
    ! [A_25] : k2_tarski(A_25,A_25) = k1_tarski(A_25) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_40,plain,(
    ! [A_28,B_29,C_30] : k2_enumset1(A_28,A_28,B_29,C_30) = k1_enumset1(A_28,B_29,C_30) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_128,plain,(
    ! [A_63,B_64,C_65,D_66] : k2_xboole_0(k1_enumset1(A_63,B_64,C_65),k1_tarski(D_66)) = k2_enumset1(A_63,B_64,C_65,D_66) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_137,plain,(
    ! [A_26,B_27,D_66] : k2_xboole_0(k2_tarski(A_26,B_27),k1_tarski(D_66)) = k2_enumset1(A_26,A_26,B_27,D_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_128])).

tff(c_141,plain,(
    ! [A_67,B_68,D_69] : k2_xboole_0(k2_tarski(A_67,B_68),k1_tarski(D_69)) = k1_enumset1(A_67,B_68,D_69) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_137])).

tff(c_150,plain,(
    ! [A_25,D_69] : k2_xboole_0(k1_tarski(A_25),k1_tarski(D_69)) = k1_enumset1(A_25,A_25,D_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_141])).

tff(c_153,plain,(
    ! [A_25,D_69] : k2_xboole_0(k1_tarski(A_25),k1_tarski(D_69)) = k2_tarski(A_25,D_69) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_150])).

tff(c_154,plain,(
    ! [A_70,D_71] : k2_xboole_0(k1_tarski(A_70),k1_tarski(D_71)) = k2_tarski(A_70,D_71) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_150])).

tff(c_46,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_160,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_46])).

tff(c_140,plain,(
    ! [A_26,B_27,D_66] : k2_xboole_0(k2_tarski(A_26,B_27),k1_tarski(D_66)) = k1_enumset1(A_26,B_27,D_66) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_137])).

tff(c_172,plain,(
    ! [D_66] : k2_xboole_0(k1_tarski('#skF_3'),k1_tarski(D_66)) = k1_enumset1('#skF_3','#skF_4',D_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_140])).

tff(c_185,plain,(
    ! [D_72] : k1_enumset1('#skF_3','#skF_4',D_72) = k2_tarski('#skF_3',D_72) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_172])).

tff(c_10,plain,(
    ! [E_11,A_5,C_7] : r2_hidden(E_11,k1_enumset1(A_5,E_11,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_197,plain,(
    ! [D_72] : r2_hidden('#skF_4',k2_tarski('#skF_3',D_72)) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_10])).

tff(c_227,plain,(
    ! [E_76,C_77,B_78,A_79] :
      ( E_76 = C_77
      | E_76 = B_78
      | E_76 = A_79
      | ~ r2_hidden(E_76,k1_enumset1(A_79,B_78,C_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_264,plain,(
    ! [E_84,B_85,A_86] :
      ( E_84 = B_85
      | E_84 = A_86
      | E_84 = A_86
      | ~ r2_hidden(E_84,k2_tarski(A_86,B_85)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_227])).

tff(c_267,plain,(
    ! [D_72] :
      ( D_72 = '#skF_4'
      | '#skF_3' = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_197,c_264])).

tff(c_287,plain,(
    ! [D_87] : D_87 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_44,c_267])).

tff(c_380,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.37  % Computer   : n024.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 18:51:21 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.38  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.30  
% 2.08/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.30  %$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.08/1.30  
% 2.08/1.30  %Foreground sorts:
% 2.08/1.30  
% 2.08/1.30  
% 2.08/1.30  %Background operators:
% 2.08/1.30  
% 2.08/1.30  
% 2.08/1.30  %Foreground operators:
% 2.08/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.08/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.08/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.08/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.08/1.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.08/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.08/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.08/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.08/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.08/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.08/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.08/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.08/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.08/1.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.08/1.30  
% 2.08/1.31  tff(f_63, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 2.08/1.31  tff(f_54, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.08/1.31  tff(f_52, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.08/1.31  tff(f_56, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.08/1.31  tff(f_48, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 2.08/1.31  tff(f_44, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.08/1.31  tff(c_44, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.08/1.31  tff(c_38, plain, (![A_26, B_27]: (k1_enumset1(A_26, A_26, B_27)=k2_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.08/1.31  tff(c_36, plain, (![A_25]: (k2_tarski(A_25, A_25)=k1_tarski(A_25))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.08/1.31  tff(c_40, plain, (![A_28, B_29, C_30]: (k2_enumset1(A_28, A_28, B_29, C_30)=k1_enumset1(A_28, B_29, C_30))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.08/1.31  tff(c_128, plain, (![A_63, B_64, C_65, D_66]: (k2_xboole_0(k1_enumset1(A_63, B_64, C_65), k1_tarski(D_66))=k2_enumset1(A_63, B_64, C_65, D_66))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.08/1.31  tff(c_137, plain, (![A_26, B_27, D_66]: (k2_xboole_0(k2_tarski(A_26, B_27), k1_tarski(D_66))=k2_enumset1(A_26, A_26, B_27, D_66))), inference(superposition, [status(thm), theory('equality')], [c_38, c_128])).
% 2.08/1.31  tff(c_141, plain, (![A_67, B_68, D_69]: (k2_xboole_0(k2_tarski(A_67, B_68), k1_tarski(D_69))=k1_enumset1(A_67, B_68, D_69))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_137])).
% 2.08/1.31  tff(c_150, plain, (![A_25, D_69]: (k2_xboole_0(k1_tarski(A_25), k1_tarski(D_69))=k1_enumset1(A_25, A_25, D_69))), inference(superposition, [status(thm), theory('equality')], [c_36, c_141])).
% 2.08/1.31  tff(c_153, plain, (![A_25, D_69]: (k2_xboole_0(k1_tarski(A_25), k1_tarski(D_69))=k2_tarski(A_25, D_69))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_150])).
% 2.08/1.31  tff(c_154, plain, (![A_70, D_71]: (k2_xboole_0(k1_tarski(A_70), k1_tarski(D_71))=k2_tarski(A_70, D_71))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_150])).
% 2.08/1.31  tff(c_46, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.08/1.31  tff(c_160, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_154, c_46])).
% 2.08/1.31  tff(c_140, plain, (![A_26, B_27, D_66]: (k2_xboole_0(k2_tarski(A_26, B_27), k1_tarski(D_66))=k1_enumset1(A_26, B_27, D_66))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_137])).
% 2.08/1.31  tff(c_172, plain, (![D_66]: (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski(D_66))=k1_enumset1('#skF_3', '#skF_4', D_66))), inference(superposition, [status(thm), theory('equality')], [c_160, c_140])).
% 2.08/1.31  tff(c_185, plain, (![D_72]: (k1_enumset1('#skF_3', '#skF_4', D_72)=k2_tarski('#skF_3', D_72))), inference(demodulation, [status(thm), theory('equality')], [c_153, c_172])).
% 2.08/1.31  tff(c_10, plain, (![E_11, A_5, C_7]: (r2_hidden(E_11, k1_enumset1(A_5, E_11, C_7)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.08/1.31  tff(c_197, plain, (![D_72]: (r2_hidden('#skF_4', k2_tarski('#skF_3', D_72)))), inference(superposition, [status(thm), theory('equality')], [c_185, c_10])).
% 2.08/1.31  tff(c_227, plain, (![E_76, C_77, B_78, A_79]: (E_76=C_77 | E_76=B_78 | E_76=A_79 | ~r2_hidden(E_76, k1_enumset1(A_79, B_78, C_77)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.08/1.31  tff(c_264, plain, (![E_84, B_85, A_86]: (E_84=B_85 | E_84=A_86 | E_84=A_86 | ~r2_hidden(E_84, k2_tarski(A_86, B_85)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_227])).
% 2.08/1.31  tff(c_267, plain, (![D_72]: (D_72='#skF_4' | '#skF_3'='#skF_4')), inference(resolution, [status(thm)], [c_197, c_264])).
% 2.08/1.31  tff(c_287, plain, (![D_87]: (D_87='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_44, c_44, c_267])).
% 2.08/1.31  tff(c_380, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_287, c_44])).
% 2.08/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.31  
% 2.08/1.31  Inference rules
% 2.08/1.31  ----------------------
% 2.08/1.31  #Ref     : 0
% 2.08/1.31  #Sup     : 101
% 2.08/1.31  #Fact    : 0
% 2.08/1.31  #Define  : 0
% 2.08/1.31  #Split   : 0
% 2.08/1.31  #Chain   : 0
% 2.08/1.31  #Close   : 0
% 2.08/1.31  
% 2.08/1.31  Ordering : KBO
% 2.08/1.31  
% 2.08/1.31  Simplification rules
% 2.08/1.31  ----------------------
% 2.08/1.31  #Subsume      : 14
% 2.08/1.31  #Demod        : 17
% 2.08/1.31  #Tautology    : 43
% 2.08/1.31  #SimpNegUnit  : 1
% 2.08/1.31  #BackRed      : 0
% 2.08/1.31  
% 2.08/1.31  #Partial instantiations: 0
% 2.08/1.31  #Strategies tried      : 1
% 2.08/1.31  
% 2.08/1.31  Timing (in seconds)
% 2.08/1.31  ----------------------
% 2.08/1.31  Preprocessing        : 0.31
% 2.08/1.31  Parsing              : 0.15
% 2.08/1.31  CNF conversion       : 0.02
% 2.08/1.31  Main loop            : 0.22
% 2.08/1.32  Inferencing          : 0.09
% 2.08/1.32  Reduction            : 0.07
% 2.08/1.32  Demodulation         : 0.05
% 2.08/1.32  BG Simplification    : 0.02
% 2.08/1.32  Subsumption          : 0.03
% 2.08/1.32  Abstraction          : 0.01
% 2.08/1.32  MUC search           : 0.00
% 2.08/1.32  Cooper               : 0.00
% 2.08/1.32  Total                : 0.55
% 2.08/1.32  Index Insertion      : 0.00
% 2.08/1.32  Index Deletion       : 0.00
% 2.08/1.32  Index Matching       : 0.00
% 2.08/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
