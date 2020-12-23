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
% DateTime   : Thu Dec  3 09:48:45 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   40 (  48 expanded)
%              Number of leaves         :   23 (  28 expanded)
%              Depth                    :    5
%              Number of atoms          :   35 (  51 expanded)
%              Number of equality atoms :   20 (  31 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(c_10,plain,(
    ! [C_9] : r2_hidden(C_9,k1_tarski(C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_48,plain,(
    ! [B_22] : r1_tarski(k1_tarski(B_22),k1_tarski(B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_88,plain,(
    ! [A_35,B_36] :
      ( k4_xboole_0(A_35,B_36) = k1_xboole_0
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_99,plain,(
    ! [B_22] : k4_xboole_0(k1_tarski(B_22),k1_tarski(B_22)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_88])).

tff(c_300,plain,(
    ! [A_54,B_55] :
      ( ~ r2_hidden(A_54,B_55)
      | k4_xboole_0(k1_tarski(A_54),B_55) != k1_tarski(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_309,plain,(
    ! [B_22] :
      ( ~ r2_hidden(B_22,k1_tarski(B_22))
      | k1_tarski(B_22) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_300])).

tff(c_313,plain,(
    ! [B_22] : k1_tarski(B_22) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_309])).

tff(c_52,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_133,plain,(
    ! [A_43,B_44] :
      ( k4_xboole_0(k1_tarski(A_43),B_44) = k1_tarski(A_43)
      | r2_hidden(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_54,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_143,plain,
    ( k1_tarski('#skF_5') = k1_xboole_0
    | r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_54])).

tff(c_157,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_143])).

tff(c_8,plain,(
    ! [C_9,A_5] :
      ( C_9 = A_5
      | ~ r2_hidden(C_9,k1_tarski(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_160,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_157,c_8])).

tff(c_164,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_160])).

tff(c_165,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_143])).

tff(c_315,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_313,c_165])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n024.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 18:23:51 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.15  
% 1.80/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.16  %$ r2_hidden > r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1
% 1.80/1.16  
% 1.80/1.16  %Foreground sorts:
% 1.80/1.16  
% 1.80/1.16  
% 1.80/1.16  %Background operators:
% 1.80/1.16  
% 1.80/1.16  
% 1.80/1.16  %Foreground operators:
% 1.80/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.80/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.80/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.80/1.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.80/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.80/1.16  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.80/1.16  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.80/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.80/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.80/1.16  tff('#skF_5', type, '#skF_5': $i).
% 1.80/1.16  tff('#skF_6', type, '#skF_6': $i).
% 1.80/1.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.80/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.80/1.16  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.80/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.80/1.16  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.80/1.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.80/1.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.80/1.16  
% 1.80/1.16  tff(f_38, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.80/1.16  tff(f_62, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 1.80/1.16  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.80/1.16  tff(f_56, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 1.80/1.16  tff(f_67, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 1.80/1.16  tff(c_10, plain, (![C_9]: (r2_hidden(C_9, k1_tarski(C_9)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.80/1.16  tff(c_48, plain, (![B_22]: (r1_tarski(k1_tarski(B_22), k1_tarski(B_22)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.80/1.16  tff(c_88, plain, (![A_35, B_36]: (k4_xboole_0(A_35, B_36)=k1_xboole_0 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.80/1.16  tff(c_99, plain, (![B_22]: (k4_xboole_0(k1_tarski(B_22), k1_tarski(B_22))=k1_xboole_0)), inference(resolution, [status(thm)], [c_48, c_88])).
% 1.80/1.16  tff(c_300, plain, (![A_54, B_55]: (~r2_hidden(A_54, B_55) | k4_xboole_0(k1_tarski(A_54), B_55)!=k1_tarski(A_54))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.80/1.16  tff(c_309, plain, (![B_22]: (~r2_hidden(B_22, k1_tarski(B_22)) | k1_tarski(B_22)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_99, c_300])).
% 1.80/1.16  tff(c_313, plain, (![B_22]: (k1_tarski(B_22)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_309])).
% 1.80/1.16  tff(c_52, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.80/1.16  tff(c_133, plain, (![A_43, B_44]: (k4_xboole_0(k1_tarski(A_43), B_44)=k1_tarski(A_43) | r2_hidden(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.80/1.17  tff(c_54, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.80/1.17  tff(c_143, plain, (k1_tarski('#skF_5')=k1_xboole_0 | r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_133, c_54])).
% 1.80/1.17  tff(c_157, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(splitLeft, [status(thm)], [c_143])).
% 1.80/1.17  tff(c_8, plain, (![C_9, A_5]: (C_9=A_5 | ~r2_hidden(C_9, k1_tarski(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.80/1.17  tff(c_160, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_157, c_8])).
% 1.80/1.17  tff(c_164, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_160])).
% 1.80/1.17  tff(c_165, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_143])).
% 1.80/1.17  tff(c_315, plain, $false, inference(negUnitSimplification, [status(thm)], [c_313, c_165])).
% 1.80/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.17  
% 1.80/1.17  Inference rules
% 1.80/1.17  ----------------------
% 1.80/1.17  #Ref     : 0
% 1.80/1.17  #Sup     : 58
% 1.80/1.17  #Fact    : 0
% 1.80/1.17  #Define  : 0
% 1.80/1.17  #Split   : 1
% 1.80/1.17  #Chain   : 0
% 1.80/1.17  #Close   : 0
% 1.80/1.17  
% 1.80/1.17  Ordering : KBO
% 1.80/1.17  
% 1.80/1.17  Simplification rules
% 1.80/1.17  ----------------------
% 1.80/1.17  #Subsume      : 1
% 1.80/1.17  #Demod        : 21
% 1.80/1.17  #Tautology    : 43
% 1.80/1.17  #SimpNegUnit  : 2
% 1.80/1.17  #BackRed      : 2
% 1.80/1.17  
% 1.80/1.17  #Partial instantiations: 0
% 1.80/1.17  #Strategies tried      : 1
% 1.80/1.17  
% 1.80/1.17  Timing (in seconds)
% 1.80/1.17  ----------------------
% 1.80/1.17  Preprocessing        : 0.30
% 1.80/1.17  Parsing              : 0.15
% 1.80/1.17  CNF conversion       : 0.02
% 1.80/1.17  Main loop            : 0.17
% 1.80/1.17  Inferencing          : 0.06
% 1.80/1.17  Reduction            : 0.05
% 1.80/1.17  Demodulation         : 0.04
% 1.80/1.17  BG Simplification    : 0.01
% 1.80/1.17  Subsumption          : 0.03
% 1.80/1.17  Abstraction          : 0.01
% 1.80/1.17  MUC search           : 0.00
% 1.80/1.17  Cooper               : 0.00
% 1.80/1.17  Total                : 0.49
% 1.80/1.17  Index Insertion      : 0.00
% 1.80/1.17  Index Deletion       : 0.00
% 1.80/1.17  Index Matching       : 0.00
% 1.80/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
