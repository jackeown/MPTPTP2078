%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:10 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   43 (  95 expanded)
%              Number of leaves         :   17 (  37 expanded)
%              Depth                    :    7
%              Number of atoms          :   51 ( 160 expanded)
%              Number of equality atoms :   28 (  90 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( A != k1_xboole_0
       => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
          & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(C,A))
          | r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(A,C)) )
        & ~ r1_tarski(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,
    ( k2_zfmisc_1('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0
    | k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_62,plain,(
    k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_67,plain,(
    ! [A_17,B_18,C_19] :
      ( ~ r1_tarski(k2_zfmisc_1(A_17,B_18),k2_zfmisc_1(A_17,C_19))
      | r1_tarski(B_18,C_19)
      | k1_xboole_0 = A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_70,plain,(
    ! [C_19] :
      ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_tarski('#skF_2'),C_19))
      | r1_tarski('#skF_1',C_19)
      | k1_tarski('#skF_2') = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_67])).

tff(c_75,plain,(
    ! [C_19] :
      ( r1_tarski('#skF_1',C_19)
      | k1_tarski('#skF_2') = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_70])).

tff(c_76,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_75])).

tff(c_6,plain,(
    ! [A_3] : k4_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [B_9] : k4_xboole_0(k1_tarski(B_9),k1_tarski(B_9)) != k1_tarski(B_9) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_87,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_2')) != k1_tarski('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_14])).

tff(c_96,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_6,c_87])).

tff(c_99,plain,(
    ! [C_20] : r1_tarski('#skF_1',C_20) ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_4,plain,(
    ! [A_2] :
      ( k1_xboole_0 = A_2
      | ~ r1_tarski(A_2,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_103,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_99,c_4])).

tff(c_107,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_103])).

tff(c_108,plain,(
    k2_zfmisc_1('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_114,plain,(
    ! [B_21,A_22,C_23] :
      ( ~ r1_tarski(k2_zfmisc_1(B_21,A_22),k2_zfmisc_1(C_23,A_22))
      | r1_tarski(B_21,C_23)
      | k1_xboole_0 = A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_117,plain,(
    ! [C_23] :
      ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(C_23,k1_tarski('#skF_2')))
      | r1_tarski('#skF_1',C_23)
      | k1_tarski('#skF_2') = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_114])).

tff(c_122,plain,(
    ! [C_23] :
      ( r1_tarski('#skF_1',C_23)
      | k1_tarski('#skF_2') = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_117])).

tff(c_123,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_135,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_2')) != k1_tarski('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_14])).

tff(c_144,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_6,c_135])).

tff(c_148,plain,(
    ! [C_24] : r1_tarski('#skF_1',C_24) ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_152,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_148,c_4])).

tff(c_156,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_152])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:19:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.78/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/1.20  
% 1.78/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/1.20  %$ r1_tarski > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.78/1.20  
% 1.78/1.20  %Foreground sorts:
% 1.78/1.20  
% 1.78/1.20  
% 1.78/1.20  %Background operators:
% 1.78/1.20  
% 1.78/1.20  
% 1.78/1.20  %Foreground operators:
% 1.78/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.78/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.78/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.78/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.78/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.78/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.78/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.78/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.78/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.78/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.78/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.78/1.20  
% 1.78/1.21  tff(f_61, negated_conjecture, ~(![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 1.78/1.21  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.78/1.21  tff(f_46, axiom, (![A, B, C]: ~((~(A = k1_xboole_0) & (r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(C, A)) | r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(A, C)))) & ~r1_tarski(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 1.78/1.21  tff(f_33, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 1.78/1.21  tff(f_51, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.78/1.21  tff(f_31, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.78/1.21  tff(c_20, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.78/1.21  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.78/1.21  tff(c_18, plain, (k2_zfmisc_1('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0 | k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.78/1.21  tff(c_62, plain, (k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_18])).
% 1.78/1.21  tff(c_67, plain, (![A_17, B_18, C_19]: (~r1_tarski(k2_zfmisc_1(A_17, B_18), k2_zfmisc_1(A_17, C_19)) | r1_tarski(B_18, C_19) | k1_xboole_0=A_17)), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.78/1.21  tff(c_70, plain, (![C_19]: (~r1_tarski(k1_xboole_0, k2_zfmisc_1(k1_tarski('#skF_2'), C_19)) | r1_tarski('#skF_1', C_19) | k1_tarski('#skF_2')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_62, c_67])).
% 1.78/1.21  tff(c_75, plain, (![C_19]: (r1_tarski('#skF_1', C_19) | k1_tarski('#skF_2')=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_70])).
% 1.78/1.21  tff(c_76, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_75])).
% 1.78/1.21  tff(c_6, plain, (![A_3]: (k4_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.78/1.21  tff(c_14, plain, (![B_9]: (k4_xboole_0(k1_tarski(B_9), k1_tarski(B_9))!=k1_tarski(B_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.78/1.21  tff(c_87, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_2'))!=k1_tarski('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_76, c_14])).
% 1.78/1.21  tff(c_96, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_6, c_87])).
% 1.78/1.21  tff(c_99, plain, (![C_20]: (r1_tarski('#skF_1', C_20))), inference(splitRight, [status(thm)], [c_75])).
% 1.78/1.21  tff(c_4, plain, (![A_2]: (k1_xboole_0=A_2 | ~r1_tarski(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.78/1.21  tff(c_103, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_99, c_4])).
% 1.78/1.21  tff(c_107, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_103])).
% 1.78/1.21  tff(c_108, plain, (k2_zfmisc_1('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_18])).
% 1.78/1.21  tff(c_114, plain, (![B_21, A_22, C_23]: (~r1_tarski(k2_zfmisc_1(B_21, A_22), k2_zfmisc_1(C_23, A_22)) | r1_tarski(B_21, C_23) | k1_xboole_0=A_22)), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.78/1.21  tff(c_117, plain, (![C_23]: (~r1_tarski(k1_xboole_0, k2_zfmisc_1(C_23, k1_tarski('#skF_2'))) | r1_tarski('#skF_1', C_23) | k1_tarski('#skF_2')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_108, c_114])).
% 1.78/1.21  tff(c_122, plain, (![C_23]: (r1_tarski('#skF_1', C_23) | k1_tarski('#skF_2')=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_117])).
% 1.78/1.21  tff(c_123, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_122])).
% 1.78/1.21  tff(c_135, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_2'))!=k1_tarski('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_123, c_14])).
% 1.78/1.21  tff(c_144, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_123, c_6, c_135])).
% 1.78/1.21  tff(c_148, plain, (![C_24]: (r1_tarski('#skF_1', C_24))), inference(splitRight, [status(thm)], [c_122])).
% 1.78/1.21  tff(c_152, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_148, c_4])).
% 1.78/1.21  tff(c_156, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_152])).
% 1.78/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/1.21  
% 1.78/1.21  Inference rules
% 1.78/1.21  ----------------------
% 1.78/1.21  #Ref     : 0
% 1.78/1.21  #Sup     : 30
% 1.78/1.21  #Fact    : 0
% 1.78/1.21  #Define  : 0
% 1.78/1.21  #Split   : 4
% 1.78/1.21  #Chain   : 0
% 1.78/1.21  #Close   : 0
% 1.78/1.21  
% 1.78/1.21  Ordering : KBO
% 1.78/1.21  
% 1.78/1.21  Simplification rules
% 1.78/1.21  ----------------------
% 1.78/1.21  #Subsume      : 0
% 1.78/1.21  #Demod        : 13
% 1.78/1.21  #Tautology    : 16
% 1.78/1.21  #SimpNegUnit  : 2
% 1.78/1.21  #BackRed      : 3
% 1.78/1.21  
% 1.78/1.21  #Partial instantiations: 0
% 1.78/1.21  #Strategies tried      : 1
% 1.78/1.21  
% 1.78/1.21  Timing (in seconds)
% 1.78/1.21  ----------------------
% 1.78/1.22  Preprocessing        : 0.29
% 1.78/1.22  Parsing              : 0.16
% 1.78/1.22  CNF conversion       : 0.02
% 1.78/1.22  Main loop            : 0.12
% 1.78/1.22  Inferencing          : 0.04
% 1.78/1.22  Reduction            : 0.04
% 1.78/1.22  Demodulation         : 0.03
% 1.78/1.22  BG Simplification    : 0.01
% 1.78/1.22  Subsumption          : 0.02
% 1.78/1.22  Abstraction          : 0.01
% 1.78/1.22  MUC search           : 0.00
% 1.78/1.22  Cooper               : 0.00
% 1.78/1.22  Total                : 0.44
% 1.78/1.22  Index Insertion      : 0.00
% 1.78/1.22  Index Deletion       : 0.00
% 1.78/1.22  Index Matching       : 0.00
% 1.78/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
