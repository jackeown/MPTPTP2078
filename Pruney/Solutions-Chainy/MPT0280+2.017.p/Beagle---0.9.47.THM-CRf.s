%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:26 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   29 (  36 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    5
%              Number of atoms          :   29 (  43 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k2_xboole_0(k1_zfmisc_1(A),k1_zfmisc_1(B)),k1_zfmisc_1(k2_xboole_0(A,B))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_zfmisc_1)).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_19,B_20,C_21] :
      ( r1_tarski(A_19,k2_xboole_0(B_20,C_21))
      | ~ r1_tarski(k4_xboole_0(A_19,B_20),C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    ! [A_1,B_2] : r1_tarski(A_1,k2_xboole_0(B_2,A_1)) ),
    inference(resolution,[status(thm)],[c_2,c_16])).

tff(c_10,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(k1_zfmisc_1(A_11),k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    ! [A_22,C_23,B_24] :
      ( r1_tarski(k2_xboole_0(A_22,C_23),B_24)
      | ~ r1_tarski(C_23,B_24)
      | ~ r1_tarski(A_22,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1('#skF_1'),k1_zfmisc_1('#skF_2')),k1_zfmisc_1(k2_xboole_0('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_30,plain,
    ( ~ r1_tarski(k1_zfmisc_1('#skF_2'),k1_zfmisc_1(k2_xboole_0('#skF_1','#skF_2')))
    | ~ r1_tarski(k1_zfmisc_1('#skF_1'),k1_zfmisc_1(k2_xboole_0('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_26,c_12])).

tff(c_49,plain,(
    ~ r1_tarski(k1_zfmisc_1('#skF_1'),k1_zfmisc_1(k2_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_52,plain,(
    ~ r1_tarski('#skF_1',k2_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_10,c_49])).

tff(c_56,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_52])).

tff(c_57,plain,(
    ~ r1_tarski(k1_zfmisc_1('#skF_2'),k1_zfmisc_1(k2_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_61,plain,(
    ~ r1_tarski('#skF_2',k2_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_10,c_57])).

tff(c_65,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_61])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:40:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.10  
% 1.72/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.11  %$ r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_1
% 1.72/1.11  
% 1.72/1.11  %Foreground sorts:
% 1.72/1.11  
% 1.72/1.11  
% 1.72/1.11  %Background operators:
% 1.72/1.11  
% 1.72/1.11  
% 1.72/1.11  %Foreground operators:
% 1.72/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.72/1.11  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.72/1.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.72/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.72/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.72/1.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.72/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.72/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.72/1.11  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.72/1.11  
% 1.72/1.12  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.72/1.12  tff(f_31, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 1.72/1.12  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 1.72/1.12  tff(f_33, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.72/1.12  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 1.72/1.12  tff(f_46, negated_conjecture, ~(![A, B]: r1_tarski(k2_xboole_0(k1_zfmisc_1(A), k1_zfmisc_1(B)), k1_zfmisc_1(k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_zfmisc_1)).
% 1.72/1.12  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.72/1.12  tff(c_16, plain, (![A_19, B_20, C_21]: (r1_tarski(A_19, k2_xboole_0(B_20, C_21)) | ~r1_tarski(k4_xboole_0(A_19, B_20), C_21))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.72/1.12  tff(c_24, plain, (![A_1, B_2]: (r1_tarski(A_1, k2_xboole_0(B_2, A_1)))), inference(resolution, [status(thm)], [c_2, c_16])).
% 1.72/1.12  tff(c_10, plain, (![A_11, B_12]: (r1_tarski(k1_zfmisc_1(A_11), k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.72/1.12  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.72/1.12  tff(c_26, plain, (![A_22, C_23, B_24]: (r1_tarski(k2_xboole_0(A_22, C_23), B_24) | ~r1_tarski(C_23, B_24) | ~r1_tarski(A_22, B_24))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.72/1.12  tff(c_12, plain, (~r1_tarski(k2_xboole_0(k1_zfmisc_1('#skF_1'), k1_zfmisc_1('#skF_2')), k1_zfmisc_1(k2_xboole_0('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.72/1.12  tff(c_30, plain, (~r1_tarski(k1_zfmisc_1('#skF_2'), k1_zfmisc_1(k2_xboole_0('#skF_1', '#skF_2'))) | ~r1_tarski(k1_zfmisc_1('#skF_1'), k1_zfmisc_1(k2_xboole_0('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_26, c_12])).
% 1.72/1.12  tff(c_49, plain, (~r1_tarski(k1_zfmisc_1('#skF_1'), k1_zfmisc_1(k2_xboole_0('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_30])).
% 1.72/1.12  tff(c_52, plain, (~r1_tarski('#skF_1', k2_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_10, c_49])).
% 1.72/1.12  tff(c_56, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_52])).
% 1.72/1.12  tff(c_57, plain, (~r1_tarski(k1_zfmisc_1('#skF_2'), k1_zfmisc_1(k2_xboole_0('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_30])).
% 1.72/1.12  tff(c_61, plain, (~r1_tarski('#skF_2', k2_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_10, c_57])).
% 1.72/1.12  tff(c_65, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_61])).
% 1.72/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.12  
% 1.72/1.12  Inference rules
% 1.72/1.12  ----------------------
% 1.72/1.12  #Ref     : 0
% 1.72/1.12  #Sup     : 8
% 1.72/1.12  #Fact    : 0
% 1.72/1.12  #Define  : 0
% 1.72/1.12  #Split   : 1
% 1.72/1.12  #Chain   : 0
% 1.72/1.12  #Close   : 0
% 1.72/1.12  
% 1.72/1.12  Ordering : KBO
% 1.72/1.12  
% 1.72/1.12  Simplification rules
% 1.72/1.12  ----------------------
% 1.72/1.12  #Subsume      : 0
% 1.72/1.12  #Demod        : 2
% 1.72/1.12  #Tautology    : 0
% 1.72/1.12  #SimpNegUnit  : 0
% 1.72/1.12  #BackRed      : 0
% 1.72/1.12  
% 1.72/1.12  #Partial instantiations: 0
% 1.72/1.12  #Strategies tried      : 1
% 1.72/1.12  
% 1.72/1.12  Timing (in seconds)
% 1.72/1.12  ----------------------
% 1.72/1.12  Preprocessing        : 0.26
% 1.72/1.12  Parsing              : 0.15
% 1.72/1.12  CNF conversion       : 0.01
% 1.72/1.12  Main loop            : 0.10
% 1.72/1.12  Inferencing          : 0.04
% 1.72/1.12  Reduction            : 0.03
% 1.72/1.12  Demodulation         : 0.02
% 1.72/1.12  BG Simplification    : 0.01
% 1.72/1.12  Subsumption          : 0.02
% 1.72/1.12  Abstraction          : 0.00
% 1.72/1.12  MUC search           : 0.00
% 1.72/1.12  Cooper               : 0.00
% 1.72/1.12  Total                : 0.39
% 1.72/1.12  Index Insertion      : 0.00
% 1.72/1.12  Index Deletion       : 0.00
% 1.72/1.12  Index Matching       : 0.00
% 1.72/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
