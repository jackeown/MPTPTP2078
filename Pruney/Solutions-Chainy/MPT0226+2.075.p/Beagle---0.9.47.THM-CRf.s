%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:47 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   39 (  43 expanded)
%              Number of leaves         :   24 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   34 (  43 expanded)
%              Number of equality atoms :   24 (  32 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_57,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_48,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_36,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_38,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_77,plain,(
    ! [A_33,B_34] :
      ( k2_xboole_0(A_33,B_34) = B_34
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_100,plain,(
    ! [A_39,B_40] :
      ( k2_xboole_0(A_39,B_40) = B_40
      | k4_xboole_0(A_39,B_40) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_77])).

tff(c_104,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_100])).

tff(c_28,plain,(
    ! [A_13,B_14] : k2_xboole_0(k1_tarski(A_13),k1_tarski(B_14)) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_108,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_28])).

tff(c_14,plain,(
    ! [D_12,B_8] : r2_hidden(D_12,k2_tarski(D_12,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_121,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_14])).

tff(c_30,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_136,plain,(
    ! [D_44,B_45,A_46] :
      ( D_44 = B_45
      | D_44 = A_46
      | ~ r2_hidden(D_44,k2_tarski(A_46,B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_169,plain,(
    ! [D_48,A_49] :
      ( D_48 = A_49
      | D_48 = A_49
      | ~ r2_hidden(D_48,k1_tarski(A_49)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_136])).

tff(c_172,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_121,c_169])).

tff(c_179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_36,c_172])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:31:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.17  
% 1.89/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.17  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 1.89/1.17  
% 1.89/1.17  %Foreground sorts:
% 1.89/1.17  
% 1.89/1.17  
% 1.89/1.17  %Background operators:
% 1.89/1.17  
% 1.89/1.17  
% 1.89/1.17  %Foreground operators:
% 1.89/1.17  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.89/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.89/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.89/1.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.89/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.89/1.17  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.89/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.89/1.17  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.89/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.89/1.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.89/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.89/1.17  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.89/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.89/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.89/1.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.89/1.17  
% 1.89/1.18  tff(f_57, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 1.89/1.18  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.89/1.18  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.89/1.18  tff(f_46, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 1.89/1.18  tff(f_44, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.89/1.18  tff(f_48, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.89/1.18  tff(c_36, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.89/1.18  tff(c_38, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.89/1.18  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.89/1.18  tff(c_77, plain, (![A_33, B_34]: (k2_xboole_0(A_33, B_34)=B_34 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.89/1.18  tff(c_100, plain, (![A_39, B_40]: (k2_xboole_0(A_39, B_40)=B_40 | k4_xboole_0(A_39, B_40)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_77])).
% 1.89/1.18  tff(c_104, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_38, c_100])).
% 1.89/1.18  tff(c_28, plain, (![A_13, B_14]: (k2_xboole_0(k1_tarski(A_13), k1_tarski(B_14))=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.89/1.18  tff(c_108, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_104, c_28])).
% 1.89/1.18  tff(c_14, plain, (![D_12, B_8]: (r2_hidden(D_12, k2_tarski(D_12, B_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.89/1.18  tff(c_121, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_108, c_14])).
% 1.89/1.18  tff(c_30, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.89/1.18  tff(c_136, plain, (![D_44, B_45, A_46]: (D_44=B_45 | D_44=A_46 | ~r2_hidden(D_44, k2_tarski(A_46, B_45)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.89/1.18  tff(c_169, plain, (![D_48, A_49]: (D_48=A_49 | D_48=A_49 | ~r2_hidden(D_48, k1_tarski(A_49)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_136])).
% 1.89/1.18  tff(c_172, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_121, c_169])).
% 1.89/1.18  tff(c_179, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_36, c_172])).
% 1.89/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.18  
% 1.89/1.18  Inference rules
% 1.89/1.18  ----------------------
% 1.89/1.18  #Ref     : 0
% 1.89/1.18  #Sup     : 33
% 1.89/1.18  #Fact    : 0
% 1.89/1.18  #Define  : 0
% 1.89/1.18  #Split   : 0
% 1.89/1.18  #Chain   : 0
% 1.89/1.18  #Close   : 0
% 1.89/1.18  
% 1.89/1.18  Ordering : KBO
% 1.89/1.18  
% 1.89/1.18  Simplification rules
% 1.89/1.18  ----------------------
% 1.89/1.18  #Subsume      : 0
% 1.89/1.18  #Demod        : 3
% 1.89/1.18  #Tautology    : 24
% 1.89/1.18  #SimpNegUnit  : 3
% 1.89/1.18  #BackRed      : 0
% 1.89/1.18  
% 1.89/1.18  #Partial instantiations: 0
% 1.89/1.18  #Strategies tried      : 1
% 1.89/1.18  
% 1.89/1.18  Timing (in seconds)
% 1.89/1.18  ----------------------
% 1.89/1.18  Preprocessing        : 0.30
% 1.89/1.18  Parsing              : 0.15
% 1.89/1.18  CNF conversion       : 0.02
% 1.89/1.18  Main loop            : 0.13
% 1.89/1.19  Inferencing          : 0.04
% 1.89/1.19  Reduction            : 0.04
% 1.89/1.19  Demodulation         : 0.03
% 1.89/1.19  BG Simplification    : 0.01
% 1.89/1.19  Subsumption          : 0.02
% 1.89/1.19  Abstraction          : 0.01
% 1.89/1.19  MUC search           : 0.00
% 1.89/1.19  Cooper               : 0.00
% 1.89/1.19  Total                : 0.45
% 1.89/1.19  Index Insertion      : 0.00
% 1.89/1.19  Index Deletion       : 0.00
% 1.89/1.19  Index Matching       : 0.00
% 1.89/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
