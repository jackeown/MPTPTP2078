%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:42 EST 2020

% Result     : Theorem 7.12s
% Output     : CNFRefutation 7.12s
% Verified   : 
% Statistics : Number of formulae       :   38 (  53 expanded)
%              Number of leaves         :   19 (  27 expanded)
%              Depth                    :    6
%              Number of atoms          :   39 (  72 expanded)
%              Number of equality atoms :    6 (  14 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( ( r1_tarski(A,k2_zfmisc_1(C,D))
          & r1_tarski(B,k2_zfmisc_1(E,F)) )
       => r1_tarski(k2_xboole_0(A,B),k2_zfmisc_1(k2_xboole_0(C,E),k2_xboole_0(D,F))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_xboole_1)).

tff(c_16,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_102,plain,(
    ! [C_28,A_29,B_30] : k2_xboole_0(k2_zfmisc_1(C_28,A_29),k2_zfmisc_1(C_28,B_30)) = k2_zfmisc_1(C_28,k2_xboole_0(A_29,B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_115,plain,(
    ! [A_3,C_28,A_29,B_30] :
      ( r1_tarski(A_3,k2_zfmisc_1(C_28,k2_xboole_0(A_29,B_30)))
      | ~ r1_tarski(A_3,k2_zfmisc_1(C_28,B_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_4])).

tff(c_18,plain,(
    r1_tarski('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_756,plain,(
    ! [A_53,C_54,A_55,B_56] :
      ( r1_tarski(A_53,k2_zfmisc_1(C_54,k2_xboole_0(A_55,B_56)))
      | ~ r1_tarski(A_53,k2_zfmisc_1(C_54,B_56)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_4])).

tff(c_798,plain,(
    ! [A_53,C_54,B_2,A_1] :
      ( r1_tarski(A_53,k2_zfmisc_1(C_54,k2_xboole_0(B_2,A_1)))
      | ~ r1_tarski(A_53,k2_zfmisc_1(C_54,B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_756])).

tff(c_10,plain,(
    ! [A_12,C_14,B_13] : k2_xboole_0(k2_zfmisc_1(A_12,C_14),k2_zfmisc_1(B_13,C_14)) = k2_zfmisc_1(k2_xboole_0(A_12,B_13),C_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_400,plain,(
    ! [A_39,C_40,B_41,D_42] :
      ( r1_tarski(k2_xboole_0(A_39,C_40),k2_xboole_0(B_41,D_42))
      | ~ r1_tarski(C_40,D_42)
      | ~ r1_tarski(A_39,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_5084,plain,(
    ! [A_113,B_114,A_115,C_116,C_117] :
      ( r1_tarski(k2_xboole_0(A_113,C_116),k2_zfmisc_1(k2_xboole_0(A_115,B_114),C_117))
      | ~ r1_tarski(C_116,k2_zfmisc_1(B_114,C_117))
      | ~ r1_tarski(A_113,k2_zfmisc_1(A_115,C_117)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_400])).

tff(c_14,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_1','#skF_2'),k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_5195,plain,
    ( ~ r1_tarski('#skF_2',k2_zfmisc_1('#skF_5',k2_xboole_0('#skF_4','#skF_6')))
    | ~ r1_tarski('#skF_1',k2_zfmisc_1('#skF_3',k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_5084,c_14])).

tff(c_5196,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1('#skF_3',k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_5195])).

tff(c_5199,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_798,c_5196])).

tff(c_5206,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_5199])).

tff(c_5207,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1('#skF_5',k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_5195])).

tff(c_5214,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_115,c_5207])).

tff(c_5219,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_5214])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:05:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.12/2.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.12/2.51  
% 7.12/2.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.12/2.51  %$ r1_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.12/2.51  
% 7.12/2.51  %Foreground sorts:
% 7.12/2.51  
% 7.12/2.51  
% 7.12/2.51  %Background operators:
% 7.12/2.51  
% 7.12/2.51  
% 7.12/2.51  %Foreground operators:
% 7.12/2.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.12/2.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.12/2.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.12/2.51  tff('#skF_5', type, '#skF_5': $i).
% 7.12/2.51  tff('#skF_6', type, '#skF_6': $i).
% 7.12/2.51  tff('#skF_2', type, '#skF_2': $i).
% 7.12/2.51  tff('#skF_3', type, '#skF_3': $i).
% 7.12/2.51  tff('#skF_1', type, '#skF_1': $i).
% 7.12/2.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.12/2.51  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.12/2.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.12/2.51  tff('#skF_4', type, '#skF_4': $i).
% 7.12/2.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.12/2.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.12/2.51  
% 7.12/2.52  tff(f_50, negated_conjecture, ~(![A, B, C, D, E, F]: ((r1_tarski(A, k2_zfmisc_1(C, D)) & r1_tarski(B, k2_zfmisc_1(E, F))) => r1_tarski(k2_xboole_0(A, B), k2_zfmisc_1(k2_xboole_0(C, E), k2_xboole_0(D, F))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 7.12/2.52  tff(f_43, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 7.12/2.52  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 7.12/2.52  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 7.12/2.52  tff(f_37, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_xboole_1)).
% 7.12/2.52  tff(c_16, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.12/2.52  tff(c_102, plain, (![C_28, A_29, B_30]: (k2_xboole_0(k2_zfmisc_1(C_28, A_29), k2_zfmisc_1(C_28, B_30))=k2_zfmisc_1(C_28, k2_xboole_0(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.12/2.52  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.12/2.52  tff(c_115, plain, (![A_3, C_28, A_29, B_30]: (r1_tarski(A_3, k2_zfmisc_1(C_28, k2_xboole_0(A_29, B_30))) | ~r1_tarski(A_3, k2_zfmisc_1(C_28, B_30)))), inference(superposition, [status(thm), theory('equality')], [c_102, c_4])).
% 7.12/2.52  tff(c_18, plain, (r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.12/2.52  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.12/2.52  tff(c_756, plain, (![A_53, C_54, A_55, B_56]: (r1_tarski(A_53, k2_zfmisc_1(C_54, k2_xboole_0(A_55, B_56))) | ~r1_tarski(A_53, k2_zfmisc_1(C_54, B_56)))), inference(superposition, [status(thm), theory('equality')], [c_102, c_4])).
% 7.12/2.52  tff(c_798, plain, (![A_53, C_54, B_2, A_1]: (r1_tarski(A_53, k2_zfmisc_1(C_54, k2_xboole_0(B_2, A_1))) | ~r1_tarski(A_53, k2_zfmisc_1(C_54, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_756])).
% 7.12/2.52  tff(c_10, plain, (![A_12, C_14, B_13]: (k2_xboole_0(k2_zfmisc_1(A_12, C_14), k2_zfmisc_1(B_13, C_14))=k2_zfmisc_1(k2_xboole_0(A_12, B_13), C_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.12/2.52  tff(c_400, plain, (![A_39, C_40, B_41, D_42]: (r1_tarski(k2_xboole_0(A_39, C_40), k2_xboole_0(B_41, D_42)) | ~r1_tarski(C_40, D_42) | ~r1_tarski(A_39, B_41))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.12/2.52  tff(c_5084, plain, (![A_113, B_114, A_115, C_116, C_117]: (r1_tarski(k2_xboole_0(A_113, C_116), k2_zfmisc_1(k2_xboole_0(A_115, B_114), C_117)) | ~r1_tarski(C_116, k2_zfmisc_1(B_114, C_117)) | ~r1_tarski(A_113, k2_zfmisc_1(A_115, C_117)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_400])).
% 7.12/2.52  tff(c_14, plain, (~r1_tarski(k2_xboole_0('#skF_1', '#skF_2'), k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.12/2.52  tff(c_5195, plain, (~r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', k2_xboole_0('#skF_4', '#skF_6'))) | ~r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', k2_xboole_0('#skF_4', '#skF_6')))), inference(resolution, [status(thm)], [c_5084, c_14])).
% 7.12/2.52  tff(c_5196, plain, (~r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', k2_xboole_0('#skF_4', '#skF_6')))), inference(splitLeft, [status(thm)], [c_5195])).
% 7.12/2.52  tff(c_5199, plain, (~r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_798, c_5196])).
% 7.12/2.52  tff(c_5206, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_5199])).
% 7.12/2.52  tff(c_5207, plain, (~r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', k2_xboole_0('#skF_4', '#skF_6')))), inference(splitRight, [status(thm)], [c_5195])).
% 7.12/2.52  tff(c_5214, plain, (~r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_115, c_5207])).
% 7.12/2.52  tff(c_5219, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_5214])).
% 7.12/2.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.12/2.52  
% 7.12/2.52  Inference rules
% 7.12/2.52  ----------------------
% 7.12/2.52  #Ref     : 0
% 7.12/2.52  #Sup     : 1398
% 7.12/2.52  #Fact    : 0
% 7.12/2.52  #Define  : 0
% 7.12/2.52  #Split   : 1
% 7.12/2.52  #Chain   : 0
% 7.12/2.52  #Close   : 0
% 7.12/2.52  
% 7.12/2.52  Ordering : KBO
% 7.12/2.52  
% 7.12/2.52  Simplification rules
% 7.12/2.52  ----------------------
% 7.12/2.52  #Subsume      : 123
% 7.12/2.52  #Demod        : 254
% 7.12/2.52  #Tautology    : 159
% 7.12/2.52  #SimpNegUnit  : 0
% 7.12/2.52  #BackRed      : 0
% 7.12/2.52  
% 7.12/2.52  #Partial instantiations: 0
% 7.12/2.52  #Strategies tried      : 1
% 7.12/2.52  
% 7.12/2.52  Timing (in seconds)
% 7.12/2.52  ----------------------
% 7.12/2.52  Preprocessing        : 0.27
% 7.12/2.52  Parsing              : 0.16
% 7.12/2.52  CNF conversion       : 0.02
% 7.12/2.52  Main loop            : 1.49
% 7.12/2.52  Inferencing          : 0.43
% 7.12/2.52  Reduction            : 0.77
% 7.12/2.52  Demodulation         : 0.70
% 7.12/2.52  BG Simplification    : 0.07
% 7.12/2.52  Subsumption          : 0.17
% 7.12/2.52  Abstraction          : 0.09
% 7.12/2.52  MUC search           : 0.00
% 7.12/2.52  Cooper               : 0.00
% 7.12/2.52  Total                : 1.79
% 7.12/2.52  Index Insertion      : 0.00
% 7.12/2.52  Index Deletion       : 0.00
% 7.12/2.52  Index Matching       : 0.00
% 7.12/2.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
