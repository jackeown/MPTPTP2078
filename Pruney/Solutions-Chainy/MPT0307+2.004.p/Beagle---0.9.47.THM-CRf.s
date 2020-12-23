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
% DateTime   : Thu Dec  3 09:53:52 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   22 (  25 expanded)
%              Number of leaves         :   12 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :   28 (  37 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_zfmisc_1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D) )
       => r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_10,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_12,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4,plain,(
    ! [C_6,A_4,B_5] :
      ( r1_tarski(k2_zfmisc_1(C_6,A_4),k2_zfmisc_1(C_6,B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_44,plain,(
    ! [A_17,C_18,B_19] :
      ( r1_tarski(k2_zfmisc_1(A_17,C_18),k2_zfmisc_1(B_19,C_18))
      | ~ r1_tarski(A_17,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58,plain,(
    ! [A_24,B_25,C_26,A_27] :
      ( r1_tarski(A_24,k2_zfmisc_1(B_25,C_26))
      | ~ r1_tarski(A_24,k2_zfmisc_1(A_27,C_26))
      | ~ r1_tarski(A_27,B_25) ) ),
    inference(resolution,[status(thm)],[c_44,c_2])).

tff(c_202,plain,(
    ! [C_47,A_48,B_49,B_50] :
      ( r1_tarski(k2_zfmisc_1(C_47,A_48),k2_zfmisc_1(B_49,B_50))
      | ~ r1_tarski(C_47,B_49)
      | ~ r1_tarski(A_48,B_50) ) ),
    inference(resolution,[status(thm)],[c_4,c_58])).

tff(c_8,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_3'),k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_219,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_202,c_8])).

tff(c_230,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12,c_219])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n024.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 09:26:36 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.18/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.45  
% 2.05/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.45  %$ r1_tarski > k2_zfmisc_1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.05/1.45  
% 2.05/1.45  %Foreground sorts:
% 2.05/1.45  
% 2.05/1.45  
% 2.05/1.45  %Background operators:
% 2.05/1.45  
% 2.05/1.45  
% 2.05/1.45  %Foreground operators:
% 2.05/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.05/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.05/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.05/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.05/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.05/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.05/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.45  
% 2.29/1.46  tff(f_44, negated_conjecture, ~(![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_zfmisc_1)).
% 2.29/1.46  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 2.29/1.46  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.29/1.46  tff(c_10, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.29/1.46  tff(c_12, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.29/1.46  tff(c_4, plain, (![C_6, A_4, B_5]: (r1_tarski(k2_zfmisc_1(C_6, A_4), k2_zfmisc_1(C_6, B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.29/1.46  tff(c_44, plain, (![A_17, C_18, B_19]: (r1_tarski(k2_zfmisc_1(A_17, C_18), k2_zfmisc_1(B_19, C_18)) | ~r1_tarski(A_17, B_19))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.29/1.46  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.29/1.46  tff(c_58, plain, (![A_24, B_25, C_26, A_27]: (r1_tarski(A_24, k2_zfmisc_1(B_25, C_26)) | ~r1_tarski(A_24, k2_zfmisc_1(A_27, C_26)) | ~r1_tarski(A_27, B_25))), inference(resolution, [status(thm)], [c_44, c_2])).
% 2.29/1.46  tff(c_202, plain, (![C_47, A_48, B_49, B_50]: (r1_tarski(k2_zfmisc_1(C_47, A_48), k2_zfmisc_1(B_49, B_50)) | ~r1_tarski(C_47, B_49) | ~r1_tarski(A_48, B_50))), inference(resolution, [status(thm)], [c_4, c_58])).
% 2.29/1.46  tff(c_8, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_3'), k2_zfmisc_1('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.29/1.46  tff(c_219, plain, (~r1_tarski('#skF_1', '#skF_2') | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_202, c_8])).
% 2.29/1.46  tff(c_230, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_12, c_219])).
% 2.29/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.46  
% 2.29/1.46  Inference rules
% 2.29/1.46  ----------------------
% 2.29/1.46  #Ref     : 0
% 2.29/1.46  #Sup     : 65
% 2.29/1.46  #Fact    : 0
% 2.29/1.46  #Define  : 0
% 2.29/1.46  #Split   : 2
% 2.29/1.46  #Chain   : 0
% 2.29/1.46  #Close   : 0
% 2.29/1.46  
% 2.29/1.46  Ordering : KBO
% 2.29/1.46  
% 2.29/1.46  Simplification rules
% 2.29/1.46  ----------------------
% 2.29/1.46  #Subsume      : 3
% 2.29/1.46  #Demod        : 3
% 2.29/1.46  #Tautology    : 1
% 2.29/1.46  #SimpNegUnit  : 0
% 2.29/1.46  #BackRed      : 0
% 2.29/1.46  
% 2.29/1.46  #Partial instantiations: 0
% 2.29/1.46  #Strategies tried      : 1
% 2.29/1.46  
% 2.29/1.46  Timing (in seconds)
% 2.29/1.46  ----------------------
% 2.29/1.47  Preprocessing        : 0.34
% 2.29/1.47  Parsing              : 0.21
% 2.29/1.47  CNF conversion       : 0.02
% 2.29/1.47  Main loop            : 0.29
% 2.29/1.47  Inferencing          : 0.10
% 2.29/1.47  Reduction            : 0.06
% 2.29/1.47  Demodulation         : 0.05
% 2.29/1.47  BG Simplification    : 0.02
% 2.29/1.47  Subsumption          : 0.09
% 2.29/1.47  Abstraction          : 0.01
% 2.29/1.47  MUC search           : 0.00
% 2.29/1.47  Cooper               : 0.00
% 2.29/1.47  Total                : 0.65
% 2.29/1.47  Index Insertion      : 0.00
% 2.29/1.47  Index Deletion       : 0.00
% 2.29/1.47  Index Matching       : 0.00
% 2.29/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
