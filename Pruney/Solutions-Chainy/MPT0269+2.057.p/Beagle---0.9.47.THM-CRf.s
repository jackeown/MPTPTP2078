%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:51 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   33 (  36 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   31 (  40 expanded)
%              Number of equality atoms :   15 (  23 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_30,plain,(
    k1_tarski('#skF_2') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_16,plain,(
    ! [B_13] : r1_tarski(k1_tarski(B_13),k1_tarski(B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_80,plain,(
    ! [A_28,B_29] :
      ( k2_xboole_0(A_28,B_29) = B_29
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_99,plain,(
    ! [B_13] : k2_xboole_0(k1_tarski(B_13),k1_tarski(B_13)) = k1_tarski(B_13) ),
    inference(resolution,[status(thm)],[c_16,c_80])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_34,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_140,plain,(
    ! [A_36,B_37,C_38] :
      ( r1_tarski(A_36,k2_xboole_0(B_37,C_38))
      | ~ r1_tarski(k4_xboole_0(A_36,B_37),C_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_143,plain,(
    ! [C_38] :
      ( r1_tarski('#skF_1',k2_xboole_0(k1_tarski('#skF_2'),C_38))
      | ~ r1_tarski(k1_xboole_0,C_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_140])).

tff(c_146,plain,(
    ! [C_39] : r1_tarski('#skF_1',k2_xboole_0(k1_tarski('#skF_2'),C_39)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_143])).

tff(c_153,plain,(
    r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_146])).

tff(c_14,plain,(
    ! [B_13,A_12] :
      ( k1_tarski(B_13) = A_12
      | k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,k1_tarski(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_157,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_153,c_14])).

tff(c_164,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_157])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:09:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.15  
% 1.87/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.15  %$ r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.87/1.15  
% 1.87/1.15  %Foreground sorts:
% 1.87/1.15  
% 1.87/1.15  
% 1.87/1.15  %Background operators:
% 1.87/1.15  
% 1.87/1.15  
% 1.87/1.15  %Foreground operators:
% 1.87/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.87/1.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.87/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.87/1.15  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.87/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.87/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.87/1.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.87/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.87/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.87/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.87/1.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.87/1.15  
% 1.87/1.16  tff(f_72, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 1.87/1.16  tff(f_47, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 1.87/1.16  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.87/1.16  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.87/1.16  tff(f_37, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 1.87/1.16  tff(c_32, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.87/1.16  tff(c_30, plain, (k1_tarski('#skF_2')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.87/1.16  tff(c_16, plain, (![B_13]: (r1_tarski(k1_tarski(B_13), k1_tarski(B_13)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.87/1.16  tff(c_80, plain, (![A_28, B_29]: (k2_xboole_0(A_28, B_29)=B_29 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.87/1.16  tff(c_99, plain, (![B_13]: (k2_xboole_0(k1_tarski(B_13), k1_tarski(B_13))=k1_tarski(B_13))), inference(resolution, [status(thm)], [c_16, c_80])).
% 1.87/1.16  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.87/1.16  tff(c_34, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.87/1.16  tff(c_140, plain, (![A_36, B_37, C_38]: (r1_tarski(A_36, k2_xboole_0(B_37, C_38)) | ~r1_tarski(k4_xboole_0(A_36, B_37), C_38))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.87/1.16  tff(c_143, plain, (![C_38]: (r1_tarski('#skF_1', k2_xboole_0(k1_tarski('#skF_2'), C_38)) | ~r1_tarski(k1_xboole_0, C_38))), inference(superposition, [status(thm), theory('equality')], [c_34, c_140])).
% 1.87/1.16  tff(c_146, plain, (![C_39]: (r1_tarski('#skF_1', k2_xboole_0(k1_tarski('#skF_2'), C_39)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_143])).
% 1.87/1.16  tff(c_153, plain, (r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_99, c_146])).
% 1.87/1.16  tff(c_14, plain, (![B_13, A_12]: (k1_tarski(B_13)=A_12 | k1_xboole_0=A_12 | ~r1_tarski(A_12, k1_tarski(B_13)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.87/1.16  tff(c_157, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_153, c_14])).
% 1.87/1.16  tff(c_164, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_157])).
% 1.87/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.16  
% 1.87/1.16  Inference rules
% 1.87/1.16  ----------------------
% 1.87/1.16  #Ref     : 0
% 1.87/1.16  #Sup     : 28
% 1.87/1.16  #Fact    : 0
% 1.87/1.16  #Define  : 0
% 1.87/1.16  #Split   : 0
% 1.87/1.16  #Chain   : 0
% 1.87/1.16  #Close   : 0
% 1.87/1.16  
% 1.87/1.16  Ordering : KBO
% 1.87/1.16  
% 1.87/1.16  Simplification rules
% 1.87/1.16  ----------------------
% 1.87/1.16  #Subsume      : 0
% 1.87/1.16  #Demod        : 9
% 1.87/1.16  #Tautology    : 20
% 1.87/1.16  #SimpNegUnit  : 1
% 1.87/1.16  #BackRed      : 0
% 1.87/1.16  
% 1.87/1.16  #Partial instantiations: 0
% 1.87/1.16  #Strategies tried      : 1
% 1.87/1.16  
% 1.87/1.16  Timing (in seconds)
% 1.87/1.16  ----------------------
% 1.87/1.16  Preprocessing        : 0.29
% 1.87/1.16  Parsing              : 0.15
% 1.87/1.16  CNF conversion       : 0.02
% 1.87/1.16  Main loop            : 0.12
% 1.87/1.16  Inferencing          : 0.04
% 1.87/1.16  Reduction            : 0.04
% 1.87/1.16  Demodulation         : 0.03
% 1.87/1.16  BG Simplification    : 0.01
% 1.87/1.17  Subsumption          : 0.02
% 1.87/1.17  Abstraction          : 0.01
% 1.87/1.17  MUC search           : 0.00
% 1.87/1.17  Cooper               : 0.00
% 1.87/1.17  Total                : 0.43
% 1.87/1.17  Index Insertion      : 0.00
% 1.87/1.17  Index Deletion       : 0.00
% 1.87/1.17  Index Matching       : 0.00
% 1.87/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
