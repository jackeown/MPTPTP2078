%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:27 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   35 (  46 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    5
%              Number of atoms          :   29 (  47 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(A,B)),k1_zfmisc_1(k4_xboole_0(B,A))),k1_zfmisc_1(k5_xboole_0(A,B))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_zfmisc_1)).

tff(c_239,plain,(
    ! [A_51,B_52] : k2_xboole_0(k4_xboole_0(A_51,B_52),k4_xboole_0(B_52,A_51)) = k5_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_28,plain,(
    ! [B_24,A_25] : k2_xboole_0(B_24,A_25) = k2_xboole_0(A_25,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_12,B_13] : r1_tarski(A_12,k2_xboole_0(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_43,plain,(
    ! [A_25,B_24] : r1_tarski(A_25,k2_xboole_0(B_24,A_25)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_16])).

tff(c_260,plain,(
    ! [B_52,A_51] : r1_tarski(k4_xboole_0(B_52,A_51),k5_xboole_0(A_51,B_52)) ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_43])).

tff(c_22,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(k1_zfmisc_1(A_19),k1_zfmisc_1(B_20))
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_269,plain,(
    ! [A_51,B_52] : r1_tarski(k4_xboole_0(A_51,B_52),k5_xboole_0(A_51,B_52)) ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_16])).

tff(c_345,plain,(
    ! [A_60,C_61,B_62] :
      ( r1_tarski(k2_xboole_0(A_60,C_61),B_62)
      | ~ r1_tarski(C_61,B_62)
      | ~ r1_tarski(A_60,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_24,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1'))),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_367,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2')))
    | ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_345,c_24])).

tff(c_433,plain,(
    ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_367])).

tff(c_749,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k5_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_22,c_433])).

tff(c_753,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_749])).

tff(c_754,plain,(
    ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_367])).

tff(c_1301,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_2','#skF_1'),k5_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_22,c_754])).

tff(c_1305,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_1301])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:57:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.67/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.40  
% 2.67/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.40  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.67/1.40  
% 2.67/1.40  %Foreground sorts:
% 2.67/1.40  
% 2.67/1.40  
% 2.67/1.40  %Background operators:
% 2.67/1.40  
% 2.67/1.40  
% 2.67/1.40  %Foreground operators:
% 2.67/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.67/1.40  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.67/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.67/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.67/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.67/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.67/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.67/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.40  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.67/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.67/1.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.67/1.40  
% 2.67/1.41  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 2.67/1.41  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.67/1.41  tff(f_43, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.67/1.41  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 2.67/1.41  tff(f_49, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 2.67/1.41  tff(f_58, negated_conjecture, ~(![A, B]: r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(A, B)), k1_zfmisc_1(k4_xboole_0(B, A))), k1_zfmisc_1(k5_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_zfmisc_1)).
% 2.67/1.41  tff(c_239, plain, (![A_51, B_52]: (k2_xboole_0(k4_xboole_0(A_51, B_52), k4_xboole_0(B_52, A_51))=k5_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.67/1.41  tff(c_28, plain, (![B_24, A_25]: (k2_xboole_0(B_24, A_25)=k2_xboole_0(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.67/1.41  tff(c_16, plain, (![A_12, B_13]: (r1_tarski(A_12, k2_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.67/1.41  tff(c_43, plain, (![A_25, B_24]: (r1_tarski(A_25, k2_xboole_0(B_24, A_25)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_16])).
% 2.67/1.41  tff(c_260, plain, (![B_52, A_51]: (r1_tarski(k4_xboole_0(B_52, A_51), k5_xboole_0(A_51, B_52)))), inference(superposition, [status(thm), theory('equality')], [c_239, c_43])).
% 2.67/1.41  tff(c_22, plain, (![A_19, B_20]: (r1_tarski(k1_zfmisc_1(A_19), k1_zfmisc_1(B_20)) | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.67/1.41  tff(c_269, plain, (![A_51, B_52]: (r1_tarski(k4_xboole_0(A_51, B_52), k5_xboole_0(A_51, B_52)))), inference(superposition, [status(thm), theory('equality')], [c_239, c_16])).
% 2.67/1.41  tff(c_345, plain, (![A_60, C_61, B_62]: (r1_tarski(k2_xboole_0(A_60, C_61), B_62) | ~r1_tarski(C_61, B_62) | ~r1_tarski(A_60, B_62))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.67/1.41  tff(c_24, plain, (~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1'))), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.67/1.41  tff(c_367, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2'))) | ~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_345, c_24])).
% 2.67/1.41  tff(c_433, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_367])).
% 2.67/1.41  tff(c_749, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k5_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_433])).
% 2.67/1.41  tff(c_753, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_269, c_749])).
% 2.67/1.41  tff(c_754, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_367])).
% 2.67/1.41  tff(c_1301, plain, (~r1_tarski(k4_xboole_0('#skF_2', '#skF_1'), k5_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_754])).
% 2.67/1.41  tff(c_1305, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_260, c_1301])).
% 2.67/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.41  
% 2.67/1.41  Inference rules
% 2.67/1.41  ----------------------
% 2.67/1.41  #Ref     : 0
% 2.67/1.41  #Sup     : 314
% 2.67/1.41  #Fact    : 0
% 2.67/1.41  #Define  : 0
% 2.67/1.41  #Split   : 1
% 2.67/1.41  #Chain   : 0
% 2.67/1.41  #Close   : 0
% 2.67/1.41  
% 2.67/1.41  Ordering : KBO
% 2.67/1.41  
% 2.67/1.41  Simplification rules
% 2.67/1.41  ----------------------
% 2.67/1.41  #Subsume      : 12
% 2.67/1.41  #Demod        : 207
% 2.67/1.41  #Tautology    : 197
% 2.67/1.41  #SimpNegUnit  : 0
% 2.67/1.41  #BackRed      : 0
% 2.67/1.41  
% 2.67/1.41  #Partial instantiations: 0
% 2.67/1.41  #Strategies tried      : 1
% 2.67/1.41  
% 2.67/1.41  Timing (in seconds)
% 2.67/1.41  ----------------------
% 2.67/1.41  Preprocessing        : 0.27
% 2.67/1.41  Parsing              : 0.15
% 2.67/1.41  CNF conversion       : 0.02
% 2.67/1.41  Main loop            : 0.38
% 2.67/1.41  Inferencing          : 0.12
% 2.67/1.41  Reduction            : 0.16
% 2.67/1.41  Demodulation         : 0.13
% 2.67/1.41  BG Simplification    : 0.02
% 2.67/1.41  Subsumption          : 0.06
% 2.67/1.41  Abstraction          : 0.02
% 2.67/1.41  MUC search           : 0.00
% 2.67/1.42  Cooper               : 0.00
% 2.67/1.42  Total                : 0.67
% 2.67/1.42  Index Insertion      : 0.00
% 2.67/1.42  Index Deletion       : 0.00
% 2.67/1.42  Index Matching       : 0.00
% 2.67/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
