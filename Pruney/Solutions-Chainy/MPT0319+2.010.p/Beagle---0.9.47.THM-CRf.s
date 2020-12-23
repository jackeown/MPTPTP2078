%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:11 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   40 (  54 expanded)
%              Number of leaves         :   17 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   43 (  72 expanded)
%              Number of equality atoms :   29 (  44 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( A != B
       => ( r1_xboole_0(k2_zfmisc_1(k1_tarski(A),C),k2_zfmisc_1(k1_tarski(B),D))
          & r1_xboole_0(k2_zfmisc_1(C,k1_tarski(A)),k2_zfmisc_1(D,k1_tarski(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_53,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(c_24,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_191,plain,(
    ! [A_35,B_36] :
      ( r1_xboole_0(k1_tarski(A_35),k1_tarski(B_36))
      | B_36 = A_35 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_199,plain,(
    ! [A_35,B_36] :
      ( k3_xboole_0(k1_tarski(A_35),k1_tarski(B_36)) = k1_xboole_0
      | B_36 = A_35 ) ),
    inference(resolution,[status(thm)],[c_191,c_2])).

tff(c_18,plain,(
    ! [A_8,C_10,B_9,D_11] : k3_xboole_0(k2_zfmisc_1(A_8,C_10),k2_zfmisc_1(B_9,D_11)) = k2_zfmisc_1(k3_xboole_0(A_8,B_9),k3_xboole_0(C_10,D_11)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_79,plain,(
    ! [A_22,B_23] :
      ( r1_xboole_0(k1_tarski(A_22),k1_tarski(B_23))
      | B_23 = A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_87,plain,(
    ! [A_22,B_23] :
      ( k3_xboole_0(k1_tarski(A_22),k1_tarski(B_23)) = k1_xboole_0
      | B_23 = A_22 ) ),
    inference(resolution,[status(thm)],[c_79,c_2])).

tff(c_22,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1('#skF_3',k1_tarski('#skF_1')),k2_zfmisc_1('#skF_4',k1_tarski('#skF_2')))
    | ~ r1_xboole_0(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_3'),k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_78,plain,(
    ~ r1_xboole_0(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_3'),k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_138,plain,(
    k3_xboole_0(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_3'),k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_4')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_78])).

tff(c_156,plain,(
    k2_zfmisc_1(k3_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')),k3_xboole_0('#skF_3','#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_138])).

tff(c_184,plain,
    ( k2_zfmisc_1(k1_xboole_0,k3_xboole_0('#skF_3','#skF_4')) != k1_xboole_0
    | '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_156])).

tff(c_186,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_184])).

tff(c_188,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_186])).

tff(c_189,plain,(
    ~ r1_xboole_0(k2_zfmisc_1('#skF_3',k1_tarski('#skF_1')),k2_zfmisc_1('#skF_4',k1_tarski('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_254,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_3',k1_tarski('#skF_1')),k2_zfmisc_1('#skF_4',k1_tarski('#skF_2'))) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_189])).

tff(c_276,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_3','#skF_4'),k3_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_254])).

tff(c_310,plain,
    ( k2_zfmisc_1(k3_xboole_0('#skF_3','#skF_4'),k1_xboole_0) != k1_xboole_0
    | '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_276])).

tff(c_312,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_310])).

tff(c_314,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_312])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:51:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.23  
% 1.84/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.23  %$ r1_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.05/1.23  
% 2.05/1.23  %Foreground sorts:
% 2.05/1.23  
% 2.05/1.23  
% 2.05/1.23  %Background operators:
% 2.05/1.23  
% 2.05/1.23  
% 2.05/1.23  %Foreground operators:
% 2.05/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.05/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.05/1.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.05/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.05/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.05/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.05/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.05/1.23  tff('#skF_4', type, '#skF_4': $i).
% 2.05/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.05/1.23  
% 2.05/1.24  tff(f_66, negated_conjecture, ~(![A, B, C, D]: (~(A = B) => (r1_xboole_0(k2_zfmisc_1(k1_tarski(A), C), k2_zfmisc_1(k1_tarski(B), D)) & r1_xboole_0(k2_zfmisc_1(C, k1_tarski(A)), k2_zfmisc_1(D, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t131_zfmisc_1)).
% 2.05/1.24  tff(f_47, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.05/1.24  tff(f_58, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 2.05/1.24  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.05/1.24  tff(f_53, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 2.05/1.24  tff(c_24, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.05/1.24  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.05/1.24  tff(c_191, plain, (![A_35, B_36]: (r1_xboole_0(k1_tarski(A_35), k1_tarski(B_36)) | B_36=A_35)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.05/1.24  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.05/1.24  tff(c_199, plain, (![A_35, B_36]: (k3_xboole_0(k1_tarski(A_35), k1_tarski(B_36))=k1_xboole_0 | B_36=A_35)), inference(resolution, [status(thm)], [c_191, c_2])).
% 2.05/1.24  tff(c_18, plain, (![A_8, C_10, B_9, D_11]: (k3_xboole_0(k2_zfmisc_1(A_8, C_10), k2_zfmisc_1(B_9, D_11))=k2_zfmisc_1(k3_xboole_0(A_8, B_9), k3_xboole_0(C_10, D_11)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.05/1.24  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.05/1.24  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.05/1.24  tff(c_79, plain, (![A_22, B_23]: (r1_xboole_0(k1_tarski(A_22), k1_tarski(B_23)) | B_23=A_22)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.05/1.24  tff(c_87, plain, (![A_22, B_23]: (k3_xboole_0(k1_tarski(A_22), k1_tarski(B_23))=k1_xboole_0 | B_23=A_22)), inference(resolution, [status(thm)], [c_79, c_2])).
% 2.05/1.24  tff(c_22, plain, (~r1_xboole_0(k2_zfmisc_1('#skF_3', k1_tarski('#skF_1')), k2_zfmisc_1('#skF_4', k1_tarski('#skF_2'))) | ~r1_xboole_0(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_3'), k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.05/1.24  tff(c_78, plain, (~r1_xboole_0(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_3'), k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_4'))), inference(splitLeft, [status(thm)], [c_22])).
% 2.05/1.24  tff(c_138, plain, (k3_xboole_0(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_3'), k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_4'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_78])).
% 2.05/1.24  tff(c_156, plain, (k2_zfmisc_1(k3_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2')), k3_xboole_0('#skF_3', '#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_18, c_138])).
% 2.05/1.24  tff(c_184, plain, (k2_zfmisc_1(k1_xboole_0, k3_xboole_0('#skF_3', '#skF_4'))!=k1_xboole_0 | '#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_87, c_156])).
% 2.05/1.24  tff(c_186, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_184])).
% 2.05/1.24  tff(c_188, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_186])).
% 2.05/1.24  tff(c_189, plain, (~r1_xboole_0(k2_zfmisc_1('#skF_3', k1_tarski('#skF_1')), k2_zfmisc_1('#skF_4', k1_tarski('#skF_2')))), inference(splitRight, [status(thm)], [c_22])).
% 2.05/1.24  tff(c_254, plain, (k3_xboole_0(k2_zfmisc_1('#skF_3', k1_tarski('#skF_1')), k2_zfmisc_1('#skF_4', k1_tarski('#skF_2')))!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_189])).
% 2.05/1.24  tff(c_276, plain, (k2_zfmisc_1(k3_xboole_0('#skF_3', '#skF_4'), k3_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_18, c_254])).
% 2.05/1.24  tff(c_310, plain, (k2_zfmisc_1(k3_xboole_0('#skF_3', '#skF_4'), k1_xboole_0)!=k1_xboole_0 | '#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_199, c_276])).
% 2.05/1.24  tff(c_312, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_310])).
% 2.05/1.24  tff(c_314, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_312])).
% 2.05/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.24  
% 2.05/1.24  Inference rules
% 2.05/1.24  ----------------------
% 2.05/1.24  #Ref     : 2
% 2.05/1.24  #Sup     : 62
% 2.05/1.24  #Fact    : 0
% 2.05/1.24  #Define  : 0
% 2.05/1.24  #Split   : 1
% 2.05/1.24  #Chain   : 0
% 2.05/1.24  #Close   : 0
% 2.05/1.24  
% 2.05/1.24  Ordering : KBO
% 2.05/1.24  
% 2.05/1.24  Simplification rules
% 2.05/1.24  ----------------------
% 2.05/1.24  #Subsume      : 6
% 2.05/1.24  #Demod        : 4
% 2.05/1.24  #Tautology    : 35
% 2.05/1.24  #SimpNegUnit  : 2
% 2.05/1.24  #BackRed      : 2
% 2.05/1.24  
% 2.05/1.24  #Partial instantiations: 0
% 2.05/1.24  #Strategies tried      : 1
% 2.05/1.24  
% 2.05/1.24  Timing (in seconds)
% 2.05/1.24  ----------------------
% 2.05/1.24  Preprocessing        : 0.30
% 2.05/1.24  Parsing              : 0.15
% 2.05/1.24  CNF conversion       : 0.02
% 2.05/1.24  Main loop            : 0.19
% 2.05/1.25  Inferencing          : 0.07
% 2.05/1.25  Reduction            : 0.06
% 2.05/1.25  Demodulation         : 0.04
% 2.05/1.25  BG Simplification    : 0.01
% 2.05/1.25  Subsumption          : 0.04
% 2.05/1.25  Abstraction          : 0.01
% 2.05/1.25  MUC search           : 0.00
% 2.05/1.25  Cooper               : 0.00
% 2.05/1.25  Total                : 0.51
% 2.05/1.25  Index Insertion      : 0.00
% 2.05/1.25  Index Deletion       : 0.00
% 2.05/1.25  Index Matching       : 0.00
% 2.05/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
