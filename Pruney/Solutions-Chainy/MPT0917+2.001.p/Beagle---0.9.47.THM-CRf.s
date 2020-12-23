%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:14 EST 2020

% Result     : Theorem 12.81s
% Output     : CNFRefutation 12.81s
% Verified   : 
% Statistics : Number of formulae       :   37 (  52 expanded)
%              Number of leaves         :   16 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :   53 (  88 expanded)
%              Number of equality atoms :    2 (   8 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D)
          & r1_tarski(E,F) )
       => r1_tarski(k3_zfmisc_1(A,C,E),k3_zfmisc_1(B,D,F)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_mcart_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(c_14,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_16,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4,plain,(
    ! [C_6,A_4,B_5] :
      ( r1_tarski(k2_zfmisc_1(C_6,A_4),k2_zfmisc_1(C_6,B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_64,plain,(
    ! [A_21,C_22,B_23] :
      ( r1_tarski(k2_zfmisc_1(A_21,C_22),k2_zfmisc_1(B_23,C_22))
      | ~ r1_tarski(A_21,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_149,plain,(
    ! [A_46,B_47,C_48,A_49] :
      ( r1_tarski(A_46,k2_zfmisc_1(B_47,C_48))
      | ~ r1_tarski(A_46,k2_zfmisc_1(A_49,C_48))
      | ~ r1_tarski(A_49,B_47) ) ),
    inference(resolution,[status(thm)],[c_64,c_2])).

tff(c_156,plain,(
    ! [C_6,A_4,B_47,B_5] :
      ( r1_tarski(k2_zfmisc_1(C_6,A_4),k2_zfmisc_1(B_47,B_5))
      | ~ r1_tarski(C_6,B_47)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(resolution,[status(thm)],[c_4,c_149])).

tff(c_12,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9] : k2_zfmisc_1(k2_zfmisc_1(A_7,B_8),C_9) = k3_zfmisc_1(A_7,B_8,C_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_158,plain,(
    ! [A_50,B_51,C_52,B_53] :
      ( r1_tarski(k3_zfmisc_1(A_50,B_51,C_52),k2_zfmisc_1(B_53,C_52))
      | ~ r1_tarski(k2_zfmisc_1(A_50,B_51),B_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_64])).

tff(c_2395,plain,(
    ! [A_229,C_228,B_227,A_226,B_230] :
      ( r1_tarski(k3_zfmisc_1(A_226,B_230,C_228),k3_zfmisc_1(A_229,B_227,C_228))
      | ~ r1_tarski(k2_zfmisc_1(A_226,B_230),k2_zfmisc_1(A_229,B_227)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_158])).

tff(c_77,plain,(
    ! [C_24,A_25,B_26] :
      ( r1_tarski(k2_zfmisc_1(C_24,A_25),k2_zfmisc_1(C_24,B_26))
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_139,plain,(
    ! [A_42,C_43,B_44,A_45] :
      ( r1_tarski(A_42,k2_zfmisc_1(C_43,B_44))
      | ~ r1_tarski(A_42,k2_zfmisc_1(C_43,A_45))
      | ~ r1_tarski(A_45,B_44) ) ),
    inference(resolution,[status(thm)],[c_77,c_2])).

tff(c_145,plain,(
    ! [A_42,A_7,B_8,C_9,B_44] :
      ( r1_tarski(A_42,k2_zfmisc_1(k2_zfmisc_1(A_7,B_8),B_44))
      | ~ r1_tarski(A_42,k3_zfmisc_1(A_7,B_8,C_9))
      | ~ r1_tarski(C_9,B_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_139])).

tff(c_148,plain,(
    ! [A_42,A_7,B_8,C_9,B_44] :
      ( r1_tarski(A_42,k3_zfmisc_1(A_7,B_8,B_44))
      | ~ r1_tarski(A_42,k3_zfmisc_1(A_7,B_8,C_9))
      | ~ r1_tarski(C_9,B_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_145])).

tff(c_12593,plain,(
    ! [B_681,B_680,A_685,C_684,A_682,B_683] :
      ( r1_tarski(k3_zfmisc_1(A_685,B_681,C_684),k3_zfmisc_1(A_682,B_680,B_683))
      | ~ r1_tarski(C_684,B_683)
      | ~ r1_tarski(k2_zfmisc_1(A_685,B_681),k2_zfmisc_1(A_682,B_680)) ) ),
    inference(resolution,[status(thm)],[c_2395,c_148])).

tff(c_10,plain,(
    ~ r1_tarski(k3_zfmisc_1('#skF_1','#skF_3','#skF_5'),k3_zfmisc_1('#skF_2','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_12656,plain,
    ( ~ r1_tarski('#skF_5','#skF_6')
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_3'),k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_12593,c_10])).

tff(c_12697,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_3'),k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12656])).

tff(c_12718,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_156,c_12697])).

tff(c_12735,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16,c_12718])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:19:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.81/6.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.81/6.50  
% 12.81/6.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.81/6.50  %$ r1_tarski > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 12.81/6.50  
% 12.81/6.50  %Foreground sorts:
% 12.81/6.50  
% 12.81/6.50  
% 12.81/6.50  %Background operators:
% 12.81/6.50  
% 12.81/6.50  
% 12.81/6.50  %Foreground operators:
% 12.81/6.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.81/6.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.81/6.50  tff('#skF_5', type, '#skF_5': $i).
% 12.81/6.50  tff('#skF_6', type, '#skF_6': $i).
% 12.81/6.50  tff('#skF_2', type, '#skF_2': $i).
% 12.81/6.50  tff('#skF_3', type, '#skF_3': $i).
% 12.81/6.50  tff('#skF_1', type, '#skF_1': $i).
% 12.81/6.50  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 12.81/6.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.81/6.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.81/6.50  tff('#skF_4', type, '#skF_4': $i).
% 12.81/6.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.81/6.50  
% 12.81/6.51  tff(f_48, negated_conjecture, ~(![A, B, C, D, E, F]: (((r1_tarski(A, B) & r1_tarski(C, D)) & r1_tarski(E, F)) => r1_tarski(k3_zfmisc_1(A, C, E), k3_zfmisc_1(B, D, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_mcart_1)).
% 12.81/6.51  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 12.81/6.51  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 12.81/6.51  tff(f_39, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 12.81/6.51  tff(c_14, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_48])).
% 12.81/6.51  tff(c_16, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 12.81/6.51  tff(c_4, plain, (![C_6, A_4, B_5]: (r1_tarski(k2_zfmisc_1(C_6, A_4), k2_zfmisc_1(C_6, B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.81/6.51  tff(c_64, plain, (![A_21, C_22, B_23]: (r1_tarski(k2_zfmisc_1(A_21, C_22), k2_zfmisc_1(B_23, C_22)) | ~r1_tarski(A_21, B_23))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.81/6.51  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.81/6.51  tff(c_149, plain, (![A_46, B_47, C_48, A_49]: (r1_tarski(A_46, k2_zfmisc_1(B_47, C_48)) | ~r1_tarski(A_46, k2_zfmisc_1(A_49, C_48)) | ~r1_tarski(A_49, B_47))), inference(resolution, [status(thm)], [c_64, c_2])).
% 12.81/6.51  tff(c_156, plain, (![C_6, A_4, B_47, B_5]: (r1_tarski(k2_zfmisc_1(C_6, A_4), k2_zfmisc_1(B_47, B_5)) | ~r1_tarski(C_6, B_47) | ~r1_tarski(A_4, B_5))), inference(resolution, [status(thm)], [c_4, c_149])).
% 12.81/6.51  tff(c_12, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_48])).
% 12.81/6.51  tff(c_8, plain, (![A_7, B_8, C_9]: (k2_zfmisc_1(k2_zfmisc_1(A_7, B_8), C_9)=k3_zfmisc_1(A_7, B_8, C_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.81/6.51  tff(c_158, plain, (![A_50, B_51, C_52, B_53]: (r1_tarski(k3_zfmisc_1(A_50, B_51, C_52), k2_zfmisc_1(B_53, C_52)) | ~r1_tarski(k2_zfmisc_1(A_50, B_51), B_53))), inference(superposition, [status(thm), theory('equality')], [c_8, c_64])).
% 12.81/6.51  tff(c_2395, plain, (![A_229, C_228, B_227, A_226, B_230]: (r1_tarski(k3_zfmisc_1(A_226, B_230, C_228), k3_zfmisc_1(A_229, B_227, C_228)) | ~r1_tarski(k2_zfmisc_1(A_226, B_230), k2_zfmisc_1(A_229, B_227)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_158])).
% 12.81/6.51  tff(c_77, plain, (![C_24, A_25, B_26]: (r1_tarski(k2_zfmisc_1(C_24, A_25), k2_zfmisc_1(C_24, B_26)) | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.81/6.51  tff(c_139, plain, (![A_42, C_43, B_44, A_45]: (r1_tarski(A_42, k2_zfmisc_1(C_43, B_44)) | ~r1_tarski(A_42, k2_zfmisc_1(C_43, A_45)) | ~r1_tarski(A_45, B_44))), inference(resolution, [status(thm)], [c_77, c_2])).
% 12.81/6.51  tff(c_145, plain, (![A_42, A_7, B_8, C_9, B_44]: (r1_tarski(A_42, k2_zfmisc_1(k2_zfmisc_1(A_7, B_8), B_44)) | ~r1_tarski(A_42, k3_zfmisc_1(A_7, B_8, C_9)) | ~r1_tarski(C_9, B_44))), inference(superposition, [status(thm), theory('equality')], [c_8, c_139])).
% 12.81/6.51  tff(c_148, plain, (![A_42, A_7, B_8, C_9, B_44]: (r1_tarski(A_42, k3_zfmisc_1(A_7, B_8, B_44)) | ~r1_tarski(A_42, k3_zfmisc_1(A_7, B_8, C_9)) | ~r1_tarski(C_9, B_44))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_145])).
% 12.81/6.51  tff(c_12593, plain, (![B_681, B_680, A_685, C_684, A_682, B_683]: (r1_tarski(k3_zfmisc_1(A_685, B_681, C_684), k3_zfmisc_1(A_682, B_680, B_683)) | ~r1_tarski(C_684, B_683) | ~r1_tarski(k2_zfmisc_1(A_685, B_681), k2_zfmisc_1(A_682, B_680)))), inference(resolution, [status(thm)], [c_2395, c_148])).
% 12.81/6.51  tff(c_10, plain, (~r1_tarski(k3_zfmisc_1('#skF_1', '#skF_3', '#skF_5'), k3_zfmisc_1('#skF_2', '#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 12.81/6.51  tff(c_12656, plain, (~r1_tarski('#skF_5', '#skF_6') | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_3'), k2_zfmisc_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_12593, c_10])).
% 12.81/6.51  tff(c_12697, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_3'), k2_zfmisc_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12656])).
% 12.81/6.51  tff(c_12718, plain, (~r1_tarski('#skF_1', '#skF_2') | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_156, c_12697])).
% 12.81/6.51  tff(c_12735, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_16, c_12718])).
% 12.81/6.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.81/6.51  
% 12.81/6.51  Inference rules
% 12.81/6.52  ----------------------
% 12.81/6.52  #Ref     : 0
% 12.81/6.52  #Sup     : 3986
% 12.81/6.52  #Fact    : 0
% 12.81/6.52  #Define  : 0
% 12.81/6.52  #Split   : 7
% 12.81/6.52  #Chain   : 0
% 12.81/6.52  #Close   : 0
% 12.81/6.52  
% 12.81/6.52  Ordering : KBO
% 12.81/6.52  
% 12.81/6.52  Simplification rules
% 12.81/6.52  ----------------------
% 12.81/6.52  #Subsume      : 552
% 12.81/6.52  #Demod        : 551
% 12.81/6.52  #Tautology    : 7
% 12.81/6.52  #SimpNegUnit  : 0
% 12.81/6.52  #BackRed      : 0
% 12.81/6.52  
% 12.81/6.52  #Partial instantiations: 0
% 12.81/6.52  #Strategies tried      : 1
% 12.81/6.52  
% 12.81/6.52  Timing (in seconds)
% 12.81/6.52  ----------------------
% 12.81/6.52  Preprocessing        : 0.40
% 12.81/6.52  Parsing              : 0.22
% 12.81/6.52  CNF conversion       : 0.03
% 12.81/6.52  Main loop            : 5.25
% 12.81/6.52  Inferencing          : 0.96
% 12.81/6.52  Reduction            : 0.96
% 12.81/6.52  Demodulation         : 0.64
% 12.81/6.52  BG Simplification    : 0.13
% 12.81/6.52  Subsumption          : 2.84
% 12.88/6.52  Abstraction          : 0.17
% 12.88/6.52  MUC search           : 0.00
% 12.88/6.52  Cooper               : 0.00
% 12.88/6.52  Total                : 5.69
% 12.88/6.52  Index Insertion      : 0.00
% 12.88/6.52  Index Deletion       : 0.00
% 12.88/6.52  Index Matching       : 0.00
% 12.88/6.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
