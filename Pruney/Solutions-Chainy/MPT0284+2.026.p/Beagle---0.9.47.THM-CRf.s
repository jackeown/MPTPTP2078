%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:30 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   36 (  45 expanded)
%              Number of leaves         :   19 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   36 (  52 expanded)
%              Number of equality atoms :    3 (   5 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(A,B)),k1_zfmisc_1(k4_xboole_0(B,A))),k1_zfmisc_1(k5_xboole_0(A,B))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_zfmisc_1)).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_57,plain,(
    ! [A_31,B_32] : k2_xboole_0(k4_xboole_0(A_31,B_32),k4_xboole_0(B_32,A_31)) = k5_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,k2_xboole_0(C_7,B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_66,plain,(
    ! [A_5,A_31,B_32] :
      ( r1_tarski(A_5,k5_xboole_0(A_31,B_32))
      | ~ r1_tarski(A_5,k4_xboole_0(B_32,A_31)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_10])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(k1_zfmisc_1(A_15),k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_69,plain,(
    ! [A_31,B_32] : r1_tarski(k4_xboole_0(A_31,B_32),k5_xboole_0(A_31,B_32)) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_12])).

tff(c_89,plain,(
    ! [A_38,C_39,B_40] :
      ( r1_tarski(k2_xboole_0(A_38,C_39),B_40)
      | ~ r1_tarski(C_39,B_40)
      | ~ r1_tarski(A_38,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1'))),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_102,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2')))
    | ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_89,c_20])).

tff(c_290,plain,(
    ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_293,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k5_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_18,c_290])).

tff(c_297,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_293])).

tff(c_298,plain,(
    ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_303,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_2','#skF_1'),k5_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_18,c_298])).

tff(c_306,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_2','#skF_1'),k4_xboole_0('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_66,c_303])).

tff(c_310,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_306])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:09:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.27  
% 1.96/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.28  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1
% 1.96/1.28  
% 1.96/1.28  %Foreground sorts:
% 1.96/1.28  
% 1.96/1.28  
% 1.96/1.28  %Background operators:
% 1.96/1.28  
% 1.96/1.28  
% 1.96/1.28  %Foreground operators:
% 1.96/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.96/1.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.96/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.96/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.96/1.28  tff('#skF_2', type, '#skF_2': $i).
% 1.96/1.28  tff('#skF_1', type, '#skF_1': $i).
% 1.96/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.96/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.28  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.96/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.96/1.28  
% 1.96/1.29  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.96/1.29  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 1.96/1.29  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 1.96/1.29  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 1.96/1.29  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.96/1.29  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 1.96/1.29  tff(f_54, negated_conjecture, ~(![A, B]: r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(A, B)), k1_zfmisc_1(k4_xboole_0(B, A))), k1_zfmisc_1(k5_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_zfmisc_1)).
% 1.96/1.29  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.96/1.29  tff(c_57, plain, (![A_31, B_32]: (k2_xboole_0(k4_xboole_0(A_31, B_32), k4_xboole_0(B_32, A_31))=k5_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.96/1.29  tff(c_10, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, k2_xboole_0(C_7, B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.96/1.29  tff(c_66, plain, (![A_5, A_31, B_32]: (r1_tarski(A_5, k5_xboole_0(A_31, B_32)) | ~r1_tarski(A_5, k4_xboole_0(B_32, A_31)))), inference(superposition, [status(thm), theory('equality')], [c_57, c_10])).
% 1.96/1.29  tff(c_18, plain, (![A_15, B_16]: (r1_tarski(k1_zfmisc_1(A_15), k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.96/1.29  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.96/1.29  tff(c_69, plain, (![A_31, B_32]: (r1_tarski(k4_xboole_0(A_31, B_32), k5_xboole_0(A_31, B_32)))), inference(superposition, [status(thm), theory('equality')], [c_57, c_12])).
% 1.96/1.29  tff(c_89, plain, (![A_38, C_39, B_40]: (r1_tarski(k2_xboole_0(A_38, C_39), B_40) | ~r1_tarski(C_39, B_40) | ~r1_tarski(A_38, B_40))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.96/1.29  tff(c_20, plain, (~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1'))), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.96/1.29  tff(c_102, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2'))) | ~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_89, c_20])).
% 1.96/1.29  tff(c_290, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_102])).
% 1.96/1.29  tff(c_293, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k5_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_18, c_290])).
% 1.96/1.29  tff(c_297, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_69, c_293])).
% 1.96/1.29  tff(c_298, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_102])).
% 1.96/1.29  tff(c_303, plain, (~r1_tarski(k4_xboole_0('#skF_2', '#skF_1'), k5_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_18, c_298])).
% 1.96/1.29  tff(c_306, plain, (~r1_tarski(k4_xboole_0('#skF_2', '#skF_1'), k4_xboole_0('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_66, c_303])).
% 1.96/1.29  tff(c_310, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_306])).
% 1.96/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.29  
% 1.96/1.29  Inference rules
% 1.96/1.29  ----------------------
% 1.96/1.29  #Ref     : 0
% 1.96/1.29  #Sup     : 66
% 1.96/1.29  #Fact    : 0
% 1.96/1.29  #Define  : 0
% 1.96/1.29  #Split   : 1
% 1.96/1.29  #Chain   : 0
% 1.96/1.29  #Close   : 0
% 1.96/1.29  
% 1.96/1.29  Ordering : KBO
% 1.96/1.29  
% 1.96/1.29  Simplification rules
% 1.96/1.29  ----------------------
% 1.96/1.29  #Subsume      : 1
% 1.96/1.29  #Demod        : 24
% 1.96/1.29  #Tautology    : 28
% 1.96/1.29  #SimpNegUnit  : 0
% 1.96/1.29  #BackRed      : 0
% 1.96/1.29  
% 1.96/1.29  #Partial instantiations: 0
% 1.96/1.29  #Strategies tried      : 1
% 1.96/1.29  
% 1.96/1.29  Timing (in seconds)
% 1.96/1.29  ----------------------
% 1.96/1.29  Preprocessing        : 0.26
% 1.96/1.29  Parsing              : 0.14
% 1.96/1.29  CNF conversion       : 0.02
% 1.96/1.29  Main loop            : 0.20
% 1.96/1.29  Inferencing          : 0.07
% 1.96/1.29  Reduction            : 0.06
% 1.96/1.29  Demodulation         : 0.05
% 1.96/1.29  BG Simplification    : 0.01
% 1.96/1.29  Subsumption          : 0.04
% 1.96/1.29  Abstraction          : 0.01
% 1.96/1.29  MUC search           : 0.00
% 1.96/1.29  Cooper               : 0.00
% 1.96/1.29  Total                : 0.48
% 1.96/1.29  Index Insertion      : 0.00
% 1.96/1.29  Index Deletion       : 0.00
% 1.96/1.29  Index Matching       : 0.00
% 1.96/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
