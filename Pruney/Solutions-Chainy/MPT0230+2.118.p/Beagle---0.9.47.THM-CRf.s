%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:11 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   46 (  53 expanded)
%              Number of leaves         :   24 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   51 (  69 expanded)
%              Number of equality atoms :   32 (  45 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_48,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_50,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_46,axiom,(
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
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_48,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_46,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_50,plain,(
    r1_tarski(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_63,plain,(
    ! [A_36,B_37] :
      ( k3_xboole_0(A_36,B_37) = A_36
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_67,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) = k1_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_63])).

tff(c_30,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_73,plain,(
    ! [A_39,B_40] : k1_enumset1(A_39,A_39,B_40) = k2_tarski(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_8,plain,(
    ! [E_11,A_5,B_6] : r2_hidden(E_11,k1_enumset1(A_5,B_6,E_11)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_91,plain,(
    ! [B_41,A_42] : r2_hidden(B_41,k2_tarski(A_42,B_41)) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_8])).

tff(c_94,plain,(
    ! [A_12] : r2_hidden(A_12,k1_tarski(A_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_91])).

tff(c_131,plain,(
    ! [A_53,B_54] :
      ( k4_xboole_0(k1_tarski(A_53),B_54) = k1_tarski(A_53)
      | r2_hidden(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k4_xboole_0(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_355,plain,(
    ! [A_82,B_83] :
      ( k4_xboole_0(k1_tarski(A_82),k1_tarski(A_82)) = k3_xboole_0(k1_tarski(A_82),B_83)
      | r2_hidden(A_82,B_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_4])).

tff(c_38,plain,(
    ! [A_22,B_23] :
      ( ~ r2_hidden(A_22,B_23)
      | k4_xboole_0(k1_tarski(A_22),B_23) != k1_tarski(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_390,plain,(
    ! [A_82,B_83] :
      ( ~ r2_hidden(A_82,k1_tarski(A_82))
      | k3_xboole_0(k1_tarski(A_82),B_83) != k1_tarski(A_82)
      | r2_hidden(A_82,B_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_355,c_38])).

tff(c_434,plain,(
    ! [A_84,B_85] :
      ( k3_xboole_0(k1_tarski(A_84),B_85) != k1_tarski(A_84)
      | r2_hidden(A_84,B_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_390])).

tff(c_447,plain,(
    r2_hidden('#skF_3',k2_tarski('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_434])).

tff(c_32,plain,(
    ! [A_13,B_14] : k1_enumset1(A_13,A_13,B_14) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_236,plain,(
    ! [E_65,C_66,B_67,A_68] :
      ( E_65 = C_66
      | E_65 = B_67
      | E_65 = A_68
      | ~ r2_hidden(E_65,k1_enumset1(A_68,B_67,C_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_239,plain,(
    ! [E_65,B_14,A_13] :
      ( E_65 = B_14
      | E_65 = A_13
      | E_65 = A_13
      | ~ r2_hidden(E_65,k2_tarski(A_13,B_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_236])).

tff(c_451,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_447,c_239])).

tff(c_455,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_48,c_46,c_451])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:55:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.29  
% 2.08/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.30  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
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
% 2.08/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.08/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.08/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.08/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.08/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.08/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.08/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.08/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.08/1.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.08/1.30  
% 2.08/1.31  tff(f_74, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 2.08/1.31  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.08/1.31  tff(f_48, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.08/1.31  tff(f_50, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.08/1.31  tff(f_46, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.08/1.31  tff(f_59, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 2.08/1.31  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.08/1.31  tff(c_48, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.08/1.31  tff(c_46, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.08/1.31  tff(c_50, plain, (r1_tarski(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.08/1.31  tff(c_63, plain, (![A_36, B_37]: (k3_xboole_0(A_36, B_37)=A_36 | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.08/1.31  tff(c_67, plain, (k3_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))=k1_tarski('#skF_3')), inference(resolution, [status(thm)], [c_50, c_63])).
% 2.08/1.31  tff(c_30, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.08/1.31  tff(c_73, plain, (![A_39, B_40]: (k1_enumset1(A_39, A_39, B_40)=k2_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.08/1.31  tff(c_8, plain, (![E_11, A_5, B_6]: (r2_hidden(E_11, k1_enumset1(A_5, B_6, E_11)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.08/1.31  tff(c_91, plain, (![B_41, A_42]: (r2_hidden(B_41, k2_tarski(A_42, B_41)))), inference(superposition, [status(thm), theory('equality')], [c_73, c_8])).
% 2.08/1.31  tff(c_94, plain, (![A_12]: (r2_hidden(A_12, k1_tarski(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_91])).
% 2.08/1.31  tff(c_131, plain, (![A_53, B_54]: (k4_xboole_0(k1_tarski(A_53), B_54)=k1_tarski(A_53) | r2_hidden(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.08/1.31  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k4_xboole_0(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.08/1.31  tff(c_355, plain, (![A_82, B_83]: (k4_xboole_0(k1_tarski(A_82), k1_tarski(A_82))=k3_xboole_0(k1_tarski(A_82), B_83) | r2_hidden(A_82, B_83))), inference(superposition, [status(thm), theory('equality')], [c_131, c_4])).
% 2.08/1.31  tff(c_38, plain, (![A_22, B_23]: (~r2_hidden(A_22, B_23) | k4_xboole_0(k1_tarski(A_22), B_23)!=k1_tarski(A_22))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.08/1.31  tff(c_390, plain, (![A_82, B_83]: (~r2_hidden(A_82, k1_tarski(A_82)) | k3_xboole_0(k1_tarski(A_82), B_83)!=k1_tarski(A_82) | r2_hidden(A_82, B_83))), inference(superposition, [status(thm), theory('equality')], [c_355, c_38])).
% 2.08/1.31  tff(c_434, plain, (![A_84, B_85]: (k3_xboole_0(k1_tarski(A_84), B_85)!=k1_tarski(A_84) | r2_hidden(A_84, B_85))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_390])).
% 2.08/1.31  tff(c_447, plain, (r2_hidden('#skF_3', k2_tarski('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_67, c_434])).
% 2.08/1.31  tff(c_32, plain, (![A_13, B_14]: (k1_enumset1(A_13, A_13, B_14)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.08/1.31  tff(c_236, plain, (![E_65, C_66, B_67, A_68]: (E_65=C_66 | E_65=B_67 | E_65=A_68 | ~r2_hidden(E_65, k1_enumset1(A_68, B_67, C_66)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.08/1.31  tff(c_239, plain, (![E_65, B_14, A_13]: (E_65=B_14 | E_65=A_13 | E_65=A_13 | ~r2_hidden(E_65, k2_tarski(A_13, B_14)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_236])).
% 2.08/1.31  tff(c_451, plain, ('#skF_5'='#skF_3' | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_447, c_239])).
% 2.08/1.31  tff(c_455, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_48, c_46, c_451])).
% 2.08/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.31  
% 2.08/1.31  Inference rules
% 2.08/1.31  ----------------------
% 2.08/1.31  #Ref     : 0
% 2.08/1.31  #Sup     : 97
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
% 2.08/1.31  #Subsume      : 8
% 2.08/1.31  #Demod        : 19
% 2.08/1.31  #Tautology    : 53
% 2.08/1.31  #SimpNegUnit  : 1
% 2.08/1.31  #BackRed      : 0
% 2.08/1.31  
% 2.08/1.31  #Partial instantiations: 0
% 2.08/1.31  #Strategies tried      : 1
% 2.08/1.31  
% 2.08/1.31  Timing (in seconds)
% 2.08/1.31  ----------------------
% 2.08/1.31  Preprocessing        : 0.31
% 2.08/1.31  Parsing              : 0.16
% 2.08/1.31  CNF conversion       : 0.02
% 2.08/1.31  Main loop            : 0.24
% 2.08/1.31  Inferencing          : 0.09
% 2.08/1.31  Reduction            : 0.08
% 2.08/1.31  Demodulation         : 0.05
% 2.08/1.31  BG Simplification    : 0.02
% 2.08/1.31  Subsumption          : 0.04
% 2.08/1.31  Abstraction          : 0.01
% 2.08/1.31  MUC search           : 0.00
% 2.08/1.31  Cooper               : 0.00
% 2.08/1.31  Total                : 0.58
% 2.08/1.31  Index Insertion      : 0.00
% 2.08/1.31  Index Deletion       : 0.00
% 2.08/1.31  Index Matching       : 0.00
% 2.08/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
