%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:51 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   32 (  34 expanded)
%              Number of leaves         :   20 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   27 (  33 expanded)
%              Number of equality atoms :   14 (  20 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_28,plain,(
    k1_tarski('#skF_2') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_32,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_254,plain,(
    ! [A_46,B_47,C_48] :
      ( r1_tarski(A_46,k2_xboole_0(B_47,C_48))
      | ~ r1_tarski(k4_xboole_0(A_46,B_47),C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_266,plain,(
    ! [C_48] :
      ( r1_tarski('#skF_1',k2_xboole_0(k1_tarski('#skF_2'),C_48))
      | ~ r1_tarski(k1_xboole_0,C_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_254])).

tff(c_298,plain,(
    ! [C_52] : r1_tarski('#skF_1',k2_xboole_0(k1_tarski('#skF_2'),C_52)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_266])).

tff(c_302,plain,(
    r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_298])).

tff(c_22,plain,(
    ! [B_20,A_19] :
      ( k1_tarski(B_20) = A_19
      | k1_xboole_0 = A_19
      | ~ r1_tarski(A_19,k1_tarski(B_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_305,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_302,c_22])).

tff(c_309,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_305])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:50:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.20  
% 1.91/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.20  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.91/1.20  
% 1.91/1.20  %Foreground sorts:
% 1.91/1.20  
% 1.91/1.20  
% 1.91/1.20  %Background operators:
% 1.91/1.20  
% 1.91/1.20  
% 1.91/1.20  %Foreground operators:
% 1.91/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.91/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.91/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.91/1.20  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.91/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.91/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.91/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.91/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.91/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.91/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.91/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.91/1.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.91/1.20  
% 1.91/1.21  tff(f_63, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 1.91/1.21  tff(f_29, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 1.91/1.21  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.91/1.21  tff(f_37, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 1.91/1.21  tff(f_53, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 1.91/1.21  tff(c_30, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.91/1.21  tff(c_28, plain, (k1_tarski('#skF_2')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.91/1.21  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.91/1.21  tff(c_6, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.91/1.21  tff(c_32, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.91/1.21  tff(c_254, plain, (![A_46, B_47, C_48]: (r1_tarski(A_46, k2_xboole_0(B_47, C_48)) | ~r1_tarski(k4_xboole_0(A_46, B_47), C_48))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.91/1.21  tff(c_266, plain, (![C_48]: (r1_tarski('#skF_1', k2_xboole_0(k1_tarski('#skF_2'), C_48)) | ~r1_tarski(k1_xboole_0, C_48))), inference(superposition, [status(thm), theory('equality')], [c_32, c_254])).
% 1.91/1.21  tff(c_298, plain, (![C_52]: (r1_tarski('#skF_1', k2_xboole_0(k1_tarski('#skF_2'), C_52)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_266])).
% 1.91/1.21  tff(c_302, plain, (r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4, c_298])).
% 1.91/1.21  tff(c_22, plain, (![B_20, A_19]: (k1_tarski(B_20)=A_19 | k1_xboole_0=A_19 | ~r1_tarski(A_19, k1_tarski(B_20)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.91/1.21  tff(c_305, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_302, c_22])).
% 1.91/1.21  tff(c_309, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_305])).
% 1.91/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.21  
% 1.91/1.21  Inference rules
% 1.91/1.21  ----------------------
% 1.91/1.21  #Ref     : 0
% 1.91/1.21  #Sup     : 65
% 1.91/1.21  #Fact    : 0
% 1.91/1.21  #Define  : 0
% 1.91/1.21  #Split   : 0
% 1.91/1.21  #Chain   : 0
% 1.91/1.21  #Close   : 0
% 1.91/1.21  
% 1.91/1.21  Ordering : KBO
% 1.91/1.21  
% 1.91/1.21  Simplification rules
% 1.91/1.21  ----------------------
% 1.91/1.21  #Subsume      : 0
% 1.91/1.21  #Demod        : 16
% 1.91/1.21  #Tautology    : 48
% 1.91/1.21  #SimpNegUnit  : 1
% 1.91/1.21  #BackRed      : 0
% 1.91/1.21  
% 1.91/1.21  #Partial instantiations: 0
% 1.91/1.21  #Strategies tried      : 1
% 1.91/1.21  
% 1.91/1.21  Timing (in seconds)
% 1.91/1.21  ----------------------
% 2.00/1.21  Preprocessing        : 0.29
% 2.00/1.21  Parsing              : 0.16
% 2.00/1.21  CNF conversion       : 0.02
% 2.00/1.21  Main loop            : 0.16
% 2.00/1.21  Inferencing          : 0.06
% 2.00/1.21  Reduction            : 0.06
% 2.00/1.21  Demodulation         : 0.04
% 2.00/1.21  BG Simplification    : 0.01
% 2.00/1.21  Subsumption          : 0.02
% 2.00/1.21  Abstraction          : 0.01
% 2.00/1.21  MUC search           : 0.00
% 2.00/1.21  Cooper               : 0.00
% 2.00/1.21  Total                : 0.47
% 2.00/1.21  Index Insertion      : 0.00
% 2.00/1.21  Index Deletion       : 0.00
% 2.00/1.21  Index Matching       : 0.00
% 2.00/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
