%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:52 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :   26 (  29 expanded)
%              Number of leaves         :   14 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :   32 (  41 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D) )
       => r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_14,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_12,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(k2_zfmisc_1(A_6,C_8),k2_zfmisc_1(B_7,C_8))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_46,plain,(
    ! [C_17,A_18,B_19] :
      ( r1_tarski(k2_zfmisc_1(C_17,A_18),k2_zfmisc_1(C_17,B_19))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_56,plain,(
    ! [C_23,A_24,B_25] :
      ( k2_xboole_0(k2_zfmisc_1(C_23,A_24),k2_zfmisc_1(C_23,B_25)) = k2_zfmisc_1(C_23,B_25)
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(resolution,[status(thm)],[c_46,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_90,plain,(
    ! [C_29,A_30,C_31,B_32] :
      ( r1_tarski(k2_zfmisc_1(C_29,A_30),C_31)
      | ~ r1_tarski(k2_zfmisc_1(C_29,B_32),C_31)
      | ~ r1_tarski(A_30,B_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_2])).

tff(c_104,plain,(
    ! [A_37,A_38,B_39,C_40] :
      ( r1_tarski(k2_zfmisc_1(A_37,A_38),k2_zfmisc_1(B_39,C_40))
      | ~ r1_tarski(A_38,C_40)
      | ~ r1_tarski(A_37,B_39) ) ),
    inference(resolution,[status(thm)],[c_8,c_90])).

tff(c_10,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_3'),k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_111,plain,
    ( ~ r1_tarski('#skF_3','#skF_4')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_104,c_10])).

tff(c_120,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_111])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:19:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.75/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.15  
% 1.75/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.15  %$ r1_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.75/1.15  
% 1.75/1.15  %Foreground sorts:
% 1.75/1.15  
% 1.75/1.15  
% 1.75/1.15  %Background operators:
% 1.75/1.15  
% 1.75/1.15  
% 1.75/1.15  %Foreground operators:
% 1.75/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.75/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.75/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.75/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.75/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.75/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.75/1.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.75/1.15  tff('#skF_4', type, '#skF_4': $i).
% 1.75/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.75/1.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.75/1.15  
% 1.75/1.16  tff(f_46, negated_conjecture, ~(![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_zfmisc_1)).
% 1.75/1.16  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 1.75/1.16  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.75/1.16  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 1.75/1.16  tff(c_14, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.75/1.16  tff(c_12, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.75/1.16  tff(c_8, plain, (![A_6, C_8, B_7]: (r1_tarski(k2_zfmisc_1(A_6, C_8), k2_zfmisc_1(B_7, C_8)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.75/1.16  tff(c_46, plain, (![C_17, A_18, B_19]: (r1_tarski(k2_zfmisc_1(C_17, A_18), k2_zfmisc_1(C_17, B_19)) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.75/1.16  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.75/1.16  tff(c_56, plain, (![C_23, A_24, B_25]: (k2_xboole_0(k2_zfmisc_1(C_23, A_24), k2_zfmisc_1(C_23, B_25))=k2_zfmisc_1(C_23, B_25) | ~r1_tarski(A_24, B_25))), inference(resolution, [status(thm)], [c_46, c_4])).
% 1.75/1.16  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.75/1.16  tff(c_90, plain, (![C_29, A_30, C_31, B_32]: (r1_tarski(k2_zfmisc_1(C_29, A_30), C_31) | ~r1_tarski(k2_zfmisc_1(C_29, B_32), C_31) | ~r1_tarski(A_30, B_32))), inference(superposition, [status(thm), theory('equality')], [c_56, c_2])).
% 1.75/1.16  tff(c_104, plain, (![A_37, A_38, B_39, C_40]: (r1_tarski(k2_zfmisc_1(A_37, A_38), k2_zfmisc_1(B_39, C_40)) | ~r1_tarski(A_38, C_40) | ~r1_tarski(A_37, B_39))), inference(resolution, [status(thm)], [c_8, c_90])).
% 1.75/1.16  tff(c_10, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_3'), k2_zfmisc_1('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.75/1.16  tff(c_111, plain, (~r1_tarski('#skF_3', '#skF_4') | ~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_104, c_10])).
% 1.75/1.16  tff(c_120, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_12, c_111])).
% 1.75/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.16  
% 1.75/1.16  Inference rules
% 1.75/1.16  ----------------------
% 1.75/1.16  #Ref     : 0
% 1.75/1.16  #Sup     : 27
% 1.75/1.16  #Fact    : 0
% 1.75/1.16  #Define  : 0
% 1.75/1.16  #Split   : 0
% 1.75/1.16  #Chain   : 0
% 1.75/1.16  #Close   : 0
% 1.75/1.16  
% 1.75/1.16  Ordering : KBO
% 1.75/1.16  
% 1.75/1.16  Simplification rules
% 1.75/1.16  ----------------------
% 1.75/1.16  #Subsume      : 0
% 1.75/1.16  #Demod        : 2
% 1.75/1.16  #Tautology    : 10
% 1.75/1.16  #SimpNegUnit  : 0
% 1.75/1.16  #BackRed      : 0
% 1.75/1.16  
% 1.75/1.16  #Partial instantiations: 0
% 1.75/1.16  #Strategies tried      : 1
% 1.75/1.16  
% 1.75/1.16  Timing (in seconds)
% 1.75/1.16  ----------------------
% 1.75/1.16  Preprocessing        : 0.26
% 1.75/1.17  Parsing              : 0.14
% 1.75/1.17  CNF conversion       : 0.02
% 1.75/1.17  Main loop            : 0.15
% 1.75/1.17  Inferencing          : 0.07
% 1.75/1.17  Reduction            : 0.03
% 1.75/1.17  Demodulation         : 0.03
% 1.75/1.17  BG Simplification    : 0.01
% 1.75/1.17  Subsumption          : 0.03
% 1.75/1.17  Abstraction          : 0.01
% 1.75/1.17  MUC search           : 0.00
% 1.75/1.17  Cooper               : 0.00
% 1.75/1.17  Total                : 0.44
% 1.75/1.17  Index Insertion      : 0.00
% 1.75/1.17  Index Deletion       : 0.00
% 1.75/1.17  Index Matching       : 0.00
% 1.75/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
