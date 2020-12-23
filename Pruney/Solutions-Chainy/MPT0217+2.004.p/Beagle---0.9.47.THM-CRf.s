%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:45 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   43 (  66 expanded)
%              Number of leaves         :   17 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :   46 (  99 expanded)
%              Number of equality atoms :   38 (  87 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( k2_tarski(A,B) = k2_tarski(C,D)
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_zfmisc_1)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( k1_tarski(A) = k2_tarski(B,C)
     => B = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( k1_tarski(A) = k2_tarski(B,C)
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_zfmisc_1)).

tff(c_26,plain,(
    '#skF_6' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_30,plain,(
    k2_tarski('#skF_5','#skF_6') = k2_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_60,plain,(
    ! [C_20,B_21,A_22] :
      ( C_20 = B_21
      | k2_tarski(B_21,C_20) != k1_tarski(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_63,plain,(
    ! [A_22] :
      ( '#skF_5' = '#skF_6'
      | k2_tarski('#skF_3','#skF_4') != k1_tarski(A_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_60])).

tff(c_80,plain,(
    ! [A_22] : k2_tarski('#skF_3','#skF_4') != k1_tarski(A_22) ),
    inference(splitLeft,[status(thm)],[c_63])).

tff(c_4,plain,(
    ! [D_6,A_1] : r2_hidden(D_6,k2_tarski(A_1,D_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_53,plain,(
    r2_hidden('#skF_6',k2_tarski('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_4])).

tff(c_82,plain,(
    ! [D_29,B_30,A_31] :
      ( D_29 = B_30
      | D_29 = A_31
      | ~ r2_hidden(D_29,k2_tarski(A_31,B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_88,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_6' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_53,c_82])).

tff(c_106,plain,(
    '#skF_6' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_88])).

tff(c_28,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6,plain,(
    ! [D_6,B_2] : r2_hidden(D_6,k2_tarski(D_6,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_56,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_6])).

tff(c_85,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_56,c_82])).

tff(c_103,plain,(
    '#skF_5' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_85])).

tff(c_112,plain,(
    k2_tarski('#skF_3','#skF_4') = k2_tarski('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_30])).

tff(c_126,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_106,c_112])).

tff(c_127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_126])).

tff(c_128,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_130,plain,(
    k2_tarski('#skF_6','#skF_6') = k2_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_30])).

tff(c_133,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_130])).

tff(c_22,plain,(
    ! [B_9,A_8,C_10] :
      ( B_9 = A_8
      | k2_tarski(B_9,C_10) != k1_tarski(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_143,plain,(
    ! [A_8] :
      ( A_8 = '#skF_3'
      | k1_tarski(A_8) != k1_tarski('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_22])).

tff(c_175,plain,(
    '#skF_6' = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_143])).

tff(c_177,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_175])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:47:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.74/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.16  
% 1.84/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.16  %$ r2_hidden > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 1.84/1.16  
% 1.84/1.16  %Foreground sorts:
% 1.84/1.16  
% 1.84/1.16  
% 1.84/1.16  %Background operators:
% 1.84/1.16  
% 1.84/1.16  
% 1.84/1.16  %Foreground operators:
% 1.84/1.16  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.84/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.84/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.84/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.84/1.16  tff('#skF_5', type, '#skF_5': $i).
% 1.84/1.16  tff('#skF_6', type, '#skF_6': $i).
% 1.84/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.84/1.16  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.84/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.84/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.16  
% 1.84/1.17  tff(f_54, negated_conjecture, ~(![A, B, C, D]: ~(((k2_tarski(A, B) = k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_zfmisc_1)).
% 1.84/1.17  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.84/1.17  tff(f_44, axiom, (![A, B, C]: ((k1_tarski(A) = k2_tarski(B, C)) => (B = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_zfmisc_1)).
% 1.84/1.17  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.84/1.17  tff(f_40, axiom, (![A, B, C]: ((k1_tarski(A) = k2_tarski(B, C)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_zfmisc_1)).
% 1.84/1.17  tff(c_26, plain, ('#skF_6'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.84/1.17  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.84/1.17  tff(c_30, plain, (k2_tarski('#skF_5', '#skF_6')=k2_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.84/1.17  tff(c_60, plain, (![C_20, B_21, A_22]: (C_20=B_21 | k2_tarski(B_21, C_20)!=k1_tarski(A_22))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.84/1.17  tff(c_63, plain, (![A_22]: ('#skF_5'='#skF_6' | k2_tarski('#skF_3', '#skF_4')!=k1_tarski(A_22))), inference(superposition, [status(thm), theory('equality')], [c_30, c_60])).
% 1.84/1.17  tff(c_80, plain, (![A_22]: (k2_tarski('#skF_3', '#skF_4')!=k1_tarski(A_22))), inference(splitLeft, [status(thm)], [c_63])).
% 1.84/1.17  tff(c_4, plain, (![D_6, A_1]: (r2_hidden(D_6, k2_tarski(A_1, D_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.84/1.17  tff(c_53, plain, (r2_hidden('#skF_6', k2_tarski('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_30, c_4])).
% 1.84/1.17  tff(c_82, plain, (![D_29, B_30, A_31]: (D_29=B_30 | D_29=A_31 | ~r2_hidden(D_29, k2_tarski(A_31, B_30)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.84/1.17  tff(c_88, plain, ('#skF_6'='#skF_4' | '#skF_6'='#skF_3'), inference(resolution, [status(thm)], [c_53, c_82])).
% 1.84/1.17  tff(c_106, plain, ('#skF_6'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_26, c_88])).
% 1.84/1.17  tff(c_28, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.84/1.17  tff(c_6, plain, (![D_6, B_2]: (r2_hidden(D_6, k2_tarski(D_6, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.84/1.17  tff(c_56, plain, (r2_hidden('#skF_5', k2_tarski('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_30, c_6])).
% 1.84/1.17  tff(c_85, plain, ('#skF_5'='#skF_4' | '#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_56, c_82])).
% 1.84/1.17  tff(c_103, plain, ('#skF_5'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_28, c_85])).
% 1.84/1.17  tff(c_112, plain, (k2_tarski('#skF_3', '#skF_4')=k2_tarski('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_30])).
% 1.84/1.17  tff(c_126, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_106, c_112])).
% 1.84/1.17  tff(c_127, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_126])).
% 1.84/1.17  tff(c_128, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_63])).
% 1.84/1.17  tff(c_130, plain, (k2_tarski('#skF_6', '#skF_6')=k2_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_30])).
% 1.84/1.17  tff(c_133, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_130])).
% 1.84/1.17  tff(c_22, plain, (![B_9, A_8, C_10]: (B_9=A_8 | k2_tarski(B_9, C_10)!=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.84/1.17  tff(c_143, plain, (![A_8]: (A_8='#skF_3' | k1_tarski(A_8)!=k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_133, c_22])).
% 1.84/1.17  tff(c_175, plain, ('#skF_6'='#skF_3'), inference(reflexivity, [status(thm), theory('equality')], [c_143])).
% 1.84/1.17  tff(c_177, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_175])).
% 1.84/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.17  
% 1.84/1.17  Inference rules
% 1.84/1.17  ----------------------
% 1.84/1.17  #Ref     : 2
% 1.84/1.17  #Sup     : 34
% 1.84/1.17  #Fact    : 0
% 1.84/1.17  #Define  : 0
% 1.84/1.17  #Split   : 1
% 1.84/1.17  #Chain   : 0
% 1.84/1.17  #Close   : 0
% 1.84/1.17  
% 1.84/1.17  Ordering : KBO
% 1.84/1.17  
% 1.84/1.17  Simplification rules
% 1.84/1.17  ----------------------
% 1.84/1.17  #Subsume      : 3
% 1.84/1.17  #Demod        : 17
% 1.84/1.17  #Tautology    : 23
% 1.84/1.17  #SimpNegUnit  : 4
% 1.84/1.17  #BackRed      : 9
% 1.84/1.17  
% 1.84/1.17  #Partial instantiations: 0
% 1.84/1.17  #Strategies tried      : 1
% 1.84/1.17  
% 1.84/1.17  Timing (in seconds)
% 1.84/1.17  ----------------------
% 1.84/1.18  Preprocessing        : 0.28
% 1.84/1.18  Parsing              : 0.14
% 1.84/1.18  CNF conversion       : 0.02
% 1.84/1.18  Main loop            : 0.15
% 1.84/1.18  Inferencing          : 0.04
% 1.84/1.18  Reduction            : 0.04
% 1.84/1.18  Demodulation         : 0.03
% 1.84/1.18  BG Simplification    : 0.01
% 1.84/1.18  Subsumption          : 0.03
% 1.84/1.18  Abstraction          : 0.01
% 1.84/1.18  MUC search           : 0.00
% 1.84/1.18  Cooper               : 0.00
% 1.84/1.18  Total                : 0.45
% 1.84/1.18  Index Insertion      : 0.00
% 1.84/1.18  Index Deletion       : 0.00
% 1.84/1.18  Index Matching       : 0.00
% 1.84/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
