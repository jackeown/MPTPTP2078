%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:33 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   42 (  50 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   43 (  58 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k3_tarski(k3_xboole_0(A,B)),k3_xboole_0(k3_tarski(A),k3_tarski(B))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_zfmisc_1)).

tff(c_23,plain,(
    ! [B_25,A_26] : k2_xboole_0(B_25,A_26) = k2_xboole_0(A_26,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_15,B_16] : r1_tarski(A_15,k2_xboole_0(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_38,plain,(
    ! [A_26,B_25] : r1_tarski(A_26,k2_xboole_0(B_25,A_26)) ),
    inference(superposition,[status(thm),theory(equality)],[c_23,c_14])).

tff(c_8,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k4_xboole_0(B_9,A_8)) = k2_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_162,plain,(
    ! [A_44,B_45,C_46] :
      ( r1_tarski(k4_xboole_0(A_44,B_45),C_46)
      | ~ r1_tarski(A_44,k2_xboole_0(B_45,C_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_492,plain,(
    ! [A_82,B_83,C_84] :
      ( r1_tarski(k3_xboole_0(A_82,B_83),C_84)
      | ~ r1_tarski(A_82,k2_xboole_0(k4_xboole_0(A_82,B_83),C_84)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_162])).

tff(c_627,plain,(
    ! [A_91,B_92,A_93] :
      ( r1_tarski(k3_xboole_0(A_91,B_92),A_93)
      | ~ r1_tarski(A_91,k2_xboole_0(A_93,k4_xboole_0(A_91,B_92))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_492])).

tff(c_648,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k3_xboole_0(B_9,A_8),A_8)
      | ~ r1_tarski(B_9,k2_xboole_0(A_8,B_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_627])).

tff(c_670,plain,(
    ! [B_9,A_8] : r1_tarski(k3_xboole_0(B_9,A_8),A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_648])).

tff(c_18,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(k3_tarski(A_19),k3_tarski(B_20))
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_200,plain,(
    ! [A_51,B_52,C_53] :
      ( r1_tarski(A_51,k3_xboole_0(B_52,C_53))
      | ~ r1_tarski(A_51,C_53)
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    ~ r1_tarski(k3_tarski(k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k3_tarski('#skF_1'),k3_tarski('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_204,plain,
    ( ~ r1_tarski(k3_tarski(k3_xboole_0('#skF_1','#skF_2')),k3_tarski('#skF_2'))
    | ~ r1_tarski(k3_tarski(k3_xboole_0('#skF_1','#skF_2')),k3_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_200,c_20])).

tff(c_325,plain,(
    ~ r1_tarski(k3_tarski(k3_xboole_0('#skF_1','#skF_2')),k3_tarski('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_204])).

tff(c_328,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_325])).

tff(c_332,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_328])).

tff(c_333,plain,(
    ~ r1_tarski(k3_tarski(k3_xboole_0('#skF_1','#skF_2')),k3_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_204])).

tff(c_338,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_333])).

tff(c_675,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_670,c_338])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:08:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.67/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.39  
% 2.67/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.39  %$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_2 > #skF_1
% 2.67/1.39  
% 2.67/1.39  %Foreground sorts:
% 2.67/1.39  
% 2.67/1.39  
% 2.67/1.39  %Background operators:
% 2.67/1.39  
% 2.67/1.39  
% 2.67/1.39  %Foreground operators:
% 2.67/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.67/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.67/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.67/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.67/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.67/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.39  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.67/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.67/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.67/1.39  
% 2.67/1.40  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.67/1.40  tff(f_45, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.67/1.40  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.67/1.40  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.67/1.40  tff(f_41, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 2.67/1.40  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 2.67/1.40  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.67/1.40  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.67/1.40  tff(f_54, negated_conjecture, ~(![A, B]: r1_tarski(k3_tarski(k3_xboole_0(A, B)), k3_xboole_0(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_zfmisc_1)).
% 2.67/1.40  tff(c_23, plain, (![B_25, A_26]: (k2_xboole_0(B_25, A_26)=k2_xboole_0(A_26, B_25))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.67/1.40  tff(c_14, plain, (![A_15, B_16]: (r1_tarski(A_15, k2_xboole_0(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.67/1.40  tff(c_38, plain, (![A_26, B_25]: (r1_tarski(A_26, k2_xboole_0(B_25, A_26)))), inference(superposition, [status(thm), theory('equality')], [c_23, c_14])).
% 2.67/1.40  tff(c_8, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k4_xboole_0(B_9, A_8))=k2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.67/1.40  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.67/1.40  tff(c_12, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.67/1.40  tff(c_162, plain, (![A_44, B_45, C_46]: (r1_tarski(k4_xboole_0(A_44, B_45), C_46) | ~r1_tarski(A_44, k2_xboole_0(B_45, C_46)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.67/1.40  tff(c_492, plain, (![A_82, B_83, C_84]: (r1_tarski(k3_xboole_0(A_82, B_83), C_84) | ~r1_tarski(A_82, k2_xboole_0(k4_xboole_0(A_82, B_83), C_84)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_162])).
% 2.67/1.40  tff(c_627, plain, (![A_91, B_92, A_93]: (r1_tarski(k3_xboole_0(A_91, B_92), A_93) | ~r1_tarski(A_91, k2_xboole_0(A_93, k4_xboole_0(A_91, B_92))))), inference(superposition, [status(thm), theory('equality')], [c_2, c_492])).
% 2.67/1.40  tff(c_648, plain, (![B_9, A_8]: (r1_tarski(k3_xboole_0(B_9, A_8), A_8) | ~r1_tarski(B_9, k2_xboole_0(A_8, B_9)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_627])).
% 2.67/1.40  tff(c_670, plain, (![B_9, A_8]: (r1_tarski(k3_xboole_0(B_9, A_8), A_8))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_648])).
% 2.67/1.40  tff(c_18, plain, (![A_19, B_20]: (r1_tarski(k3_tarski(A_19), k3_tarski(B_20)) | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.67/1.40  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.67/1.40  tff(c_200, plain, (![A_51, B_52, C_53]: (r1_tarski(A_51, k3_xboole_0(B_52, C_53)) | ~r1_tarski(A_51, C_53) | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.67/1.40  tff(c_20, plain, (~r1_tarski(k3_tarski(k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k3_tarski('#skF_1'), k3_tarski('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.67/1.40  tff(c_204, plain, (~r1_tarski(k3_tarski(k3_xboole_0('#skF_1', '#skF_2')), k3_tarski('#skF_2')) | ~r1_tarski(k3_tarski(k3_xboole_0('#skF_1', '#skF_2')), k3_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_200, c_20])).
% 2.67/1.40  tff(c_325, plain, (~r1_tarski(k3_tarski(k3_xboole_0('#skF_1', '#skF_2')), k3_tarski('#skF_1'))), inference(splitLeft, [status(thm)], [c_204])).
% 2.67/1.40  tff(c_328, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_18, c_325])).
% 2.67/1.40  tff(c_332, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_328])).
% 2.67/1.40  tff(c_333, plain, (~r1_tarski(k3_tarski(k3_xboole_0('#skF_1', '#skF_2')), k3_tarski('#skF_2'))), inference(splitRight, [status(thm)], [c_204])).
% 2.67/1.40  tff(c_338, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_18, c_333])).
% 2.67/1.40  tff(c_675, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_670, c_338])).
% 2.67/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.40  
% 2.67/1.40  Inference rules
% 2.67/1.40  ----------------------
% 2.67/1.40  #Ref     : 0
% 2.67/1.40  #Sup     : 171
% 2.67/1.40  #Fact    : 0
% 2.67/1.40  #Define  : 0
% 2.67/1.40  #Split   : 1
% 2.67/1.40  #Chain   : 0
% 2.67/1.40  #Close   : 0
% 2.67/1.40  
% 2.67/1.40  Ordering : KBO
% 2.67/1.40  
% 2.67/1.40  Simplification rules
% 2.67/1.40  ----------------------
% 2.67/1.40  #Subsume      : 8
% 2.67/1.40  #Demod        : 53
% 2.67/1.40  #Tautology    : 52
% 2.67/1.40  #SimpNegUnit  : 0
% 2.67/1.40  #BackRed      : 1
% 2.67/1.40  
% 2.67/1.40  #Partial instantiations: 0
% 2.67/1.40  #Strategies tried      : 1
% 2.67/1.40  
% 2.67/1.40  Timing (in seconds)
% 2.67/1.40  ----------------------
% 2.67/1.40  Preprocessing        : 0.28
% 2.67/1.40  Parsing              : 0.16
% 2.67/1.40  CNF conversion       : 0.02
% 2.67/1.40  Main loop            : 0.34
% 2.67/1.40  Inferencing          : 0.12
% 2.67/1.40  Reduction            : 0.12
% 2.67/1.40  Demodulation         : 0.10
% 2.67/1.40  BG Simplification    : 0.01
% 2.67/1.40  Subsumption          : 0.07
% 2.67/1.40  Abstraction          : 0.01
% 2.67/1.40  MUC search           : 0.00
% 2.67/1.41  Cooper               : 0.00
% 2.67/1.41  Total                : 0.65
% 2.67/1.41  Index Insertion      : 0.00
% 2.67/1.41  Index Deletion       : 0.00
% 2.67/1.41  Index Matching       : 0.00
% 2.67/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
