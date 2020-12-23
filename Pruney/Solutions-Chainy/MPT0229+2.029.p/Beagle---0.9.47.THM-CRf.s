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
% DateTime   : Thu Dec  3 09:48:57 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   43 (  46 expanded)
%              Number of leaves         :   26 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   37 (  42 expanded)
%              Number of equality atoms :   26 (  29 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_50,axiom,(
    ! [A,B,C] : k4_enumset1(A,A,A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_enumset1)).

tff(f_48,axiom,(
    ! [A,B] : k3_enumset1(A,A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_enumset1)).

tff(f_46,axiom,(
    ! [A] : k1_enumset1(A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_40,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_42,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_54,plain,(
    ! [A_40,B_41] :
      ( k4_xboole_0(A_40,B_41) = k1_xboole_0
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_58,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_54])).

tff(c_85,plain,(
    ! [A_46,B_47] :
      ( r2_hidden(A_46,B_47)
      | k4_xboole_0(k1_tarski(A_46),B_47) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_93,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_85])).

tff(c_123,plain,(
    ! [A_60,B_56,E_59,C_57,D_58] : k4_enumset1(A_60,A_60,B_56,C_57,D_58,E_59) = k3_enumset1(A_60,B_56,C_57,D_58,E_59) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_34,plain,(
    ! [A_30,B_31,C_32] : k4_enumset1(A_30,A_30,A_30,A_30,B_31,C_32) = k1_enumset1(A_30,B_31,C_32) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_140,plain,(
    ! [C_64,D_65,E_66] : k3_enumset1(C_64,C_64,C_64,D_65,E_66) = k1_enumset1(C_64,D_65,E_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_34])).

tff(c_32,plain,(
    ! [A_28,B_29] : k3_enumset1(A_28,A_28,A_28,A_28,B_29) = k2_tarski(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_156,plain,(
    ! [D_67,E_68] : k1_enumset1(D_67,D_67,E_68) = k2_tarski(D_67,E_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_32])).

tff(c_30,plain,(
    ! [A_27] : k1_enumset1(A_27,A_27,A_27) = k1_tarski(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_172,plain,(
    ! [E_69] : k2_tarski(E_69,E_69) = k1_tarski(E_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_30])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( D_8 = B_4
      | D_8 = A_3
      | ~ r2_hidden(D_8,k2_tarski(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_203,plain,(
    ! [E_77,D_78] :
      ( E_77 = D_78
      | E_77 = D_78
      | ~ r2_hidden(D_78,k1_tarski(E_77)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_6])).

tff(c_209,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_93,c_203])).

tff(c_215,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_40,c_209])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 20:44:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.36  
% 1.97/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.37  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 1.97/1.37  
% 1.97/1.37  %Foreground sorts:
% 1.97/1.37  
% 1.97/1.37  
% 1.97/1.37  %Background operators:
% 1.97/1.37  
% 1.97/1.37  
% 1.97/1.37  %Foreground operators:
% 1.97/1.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.97/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.97/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.97/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.97/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.97/1.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.97/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.97/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.97/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.97/1.37  tff('#skF_3', type, '#skF_3': $i).
% 1.97/1.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.97/1.37  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.97/1.37  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.97/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.37  tff('#skF_4', type, '#skF_4': $i).
% 1.97/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.37  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.97/1.37  
% 2.15/1.38  tff(f_59, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_zfmisc_1)).
% 2.15/1.38  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.15/1.38  tff(f_54, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 2.15/1.38  tff(f_40, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 2.15/1.38  tff(f_50, axiom, (![A, B, C]: (k4_enumset1(A, A, A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_enumset1)).
% 2.15/1.38  tff(f_48, axiom, (![A, B]: (k3_enumset1(A, A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_enumset1)).
% 2.15/1.38  tff(f_46, axiom, (![A]: (k1_enumset1(A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_enumset1)).
% 2.15/1.38  tff(f_38, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.15/1.38  tff(c_40, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.15/1.38  tff(c_42, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.15/1.38  tff(c_54, plain, (![A_40, B_41]: (k4_xboole_0(A_40, B_41)=k1_xboole_0 | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.15/1.38  tff(c_58, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_54])).
% 2.15/1.38  tff(c_85, plain, (![A_46, B_47]: (r2_hidden(A_46, B_47) | k4_xboole_0(k1_tarski(A_46), B_47)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.15/1.38  tff(c_93, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_85])).
% 2.15/1.38  tff(c_123, plain, (![A_60, B_56, E_59, C_57, D_58]: (k4_enumset1(A_60, A_60, B_56, C_57, D_58, E_59)=k3_enumset1(A_60, B_56, C_57, D_58, E_59))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.15/1.38  tff(c_34, plain, (![A_30, B_31, C_32]: (k4_enumset1(A_30, A_30, A_30, A_30, B_31, C_32)=k1_enumset1(A_30, B_31, C_32))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.15/1.38  tff(c_140, plain, (![C_64, D_65, E_66]: (k3_enumset1(C_64, C_64, C_64, D_65, E_66)=k1_enumset1(C_64, D_65, E_66))), inference(superposition, [status(thm), theory('equality')], [c_123, c_34])).
% 2.15/1.38  tff(c_32, plain, (![A_28, B_29]: (k3_enumset1(A_28, A_28, A_28, A_28, B_29)=k2_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.15/1.38  tff(c_156, plain, (![D_67, E_68]: (k1_enumset1(D_67, D_67, E_68)=k2_tarski(D_67, E_68))), inference(superposition, [status(thm), theory('equality')], [c_140, c_32])).
% 2.15/1.38  tff(c_30, plain, (![A_27]: (k1_enumset1(A_27, A_27, A_27)=k1_tarski(A_27))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.15/1.38  tff(c_172, plain, (![E_69]: (k2_tarski(E_69, E_69)=k1_tarski(E_69))), inference(superposition, [status(thm), theory('equality')], [c_156, c_30])).
% 2.15/1.38  tff(c_6, plain, (![D_8, B_4, A_3]: (D_8=B_4 | D_8=A_3 | ~r2_hidden(D_8, k2_tarski(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.15/1.38  tff(c_203, plain, (![E_77, D_78]: (E_77=D_78 | E_77=D_78 | ~r2_hidden(D_78, k1_tarski(E_77)))), inference(superposition, [status(thm), theory('equality')], [c_172, c_6])).
% 2.15/1.38  tff(c_209, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_93, c_203])).
% 2.15/1.38  tff(c_215, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_40, c_209])).
% 2.15/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.38  
% 2.15/1.38  Inference rules
% 2.15/1.38  ----------------------
% 2.15/1.38  #Ref     : 0
% 2.15/1.38  #Sup     : 39
% 2.15/1.38  #Fact    : 0
% 2.15/1.38  #Define  : 0
% 2.15/1.38  #Split   : 0
% 2.15/1.38  #Chain   : 0
% 2.15/1.38  #Close   : 0
% 2.15/1.38  
% 2.15/1.38  Ordering : KBO
% 2.15/1.38  
% 2.15/1.38  Simplification rules
% 2.15/1.38  ----------------------
% 2.15/1.38  #Subsume      : 0
% 2.15/1.38  #Demod        : 3
% 2.15/1.38  #Tautology    : 30
% 2.15/1.38  #SimpNegUnit  : 1
% 2.15/1.38  #BackRed      : 0
% 2.15/1.38  
% 2.15/1.38  #Partial instantiations: 0
% 2.15/1.38  #Strategies tried      : 1
% 2.15/1.38  
% 2.15/1.38  Timing (in seconds)
% 2.15/1.38  ----------------------
% 2.15/1.38  Preprocessing        : 0.37
% 2.15/1.38  Parsing              : 0.20
% 2.15/1.38  CNF conversion       : 0.02
% 2.15/1.38  Main loop            : 0.14
% 2.15/1.38  Inferencing          : 0.05
% 2.15/1.38  Reduction            : 0.05
% 2.15/1.38  Demodulation         : 0.03
% 2.15/1.38  BG Simplification    : 0.01
% 2.15/1.38  Subsumption          : 0.02
% 2.15/1.38  Abstraction          : 0.01
% 2.15/1.38  MUC search           : 0.00
% 2.15/1.38  Cooper               : 0.00
% 2.15/1.38  Total                : 0.54
% 2.15/1.38  Index Insertion      : 0.00
% 2.15/1.38  Index Deletion       : 0.00
% 2.15/1.38  Index Matching       : 0.00
% 2.15/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
